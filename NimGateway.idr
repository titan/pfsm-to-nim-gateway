module NimGateway

import Data.Maybe
import Data.List
import Data.List1
import Data.SortedMap
import Data.Strings
import System
import System.File

import Pfsm
import Pfsm.Analyser
import Pfsm.Checker
import Pfsm.Data
import Pfsm.Parser
import Pfsm.Nim
import Pfsm.Service2

indentDelta : Nat
indentDelta = 2

record AppConfig where
  constructor MkAppConfig
  src : String
  middleware : String

Show AppConfig where
  show (MkAppConfig src middleware)
    = List.join "\n" [ "src: " ++ src
                     , "middleware: " ++ (show middleware)
                     ]

middleware : String -> Maybe (List Meta) -> String
middleware defaultValue metas
  = case lookup "gateway.middleware" metas of
         Just (MVString m) => m
         _ => defaultValue

toNim : AppConfig -> Fsm -> String
toNim conf@(MkAppConfig _ mw) fsm@(MkFsm _ _ _ _ _ _ metas)
  = let name = fsm.name
        pre = camelize (toNimName name)
        display = displayName name metas
        searchable = isSearchable metas
        idfields = filter idFieldFilter fsm.model
        manyToOneFields = filter manyToOneFieldFilter fsm.model
        refereds = referenced fsm.model
        records = liftRecords fsm.model in
        join "\n\n" $ List.filter nonblank [ generateImports refereds
                                           , "const queue = " ++ (show (name ++ "-input"))
                                           , generateEventCalls pre name mw idfields fsm.events
                                           , generateDereferenceRecordFromJsons pre name records
                                           , generateGetJsonCall pre name fsm.model
                                           , generateFetchObject pre name mw fsm
                                           , generateFetchLists pre name mw fsm.states fsm.transitions
                                           , generateFetchListsByReferences pre name mw fsm.states fsm.transitions manyToOneFields
                                           , if searchable
                                                then generateStateSearchs pre name mw fsm.states fsm.transitions
                                                else ""
                                           , generateRouters pre name fsm.states fsm.transitions fsm.participants manyToOneFields searchable
                                           , generatePermissions pre name display fsm.states fsm.transitions fsm.participants manyToOneFields searchable
                                           ]
  where
    idFieldFilter : Parameter -> Bool
    idFieldFilter (_, _, ms)
      = case lookup "fsmid" ms of
             Just (MVString "calc") => True
             Just (MVString "copy") => True
             _ => False

    referenceFilter : Parameter -> Bool
    referenceFilter (_, _, metas)
      = case lookup "reference" metas of
             Just _ => True
             _ => False

    referenced: List Parameter -> List Name
    referenced ps
      = referenced' ps []
      where
        referenced' : List Parameter -> List Name -> List Name
        referenced' []                                       acc = acc
        referenced' ((_, (TRecord _ ps'), ms) :: xs)         acc = case lookup "reference" ms of
                                                                       Just (MVString dst) => referenced' xs ((dst :: acc) ++ (referenced ps'))
                                                                       _ => referenced' xs (acc ++ (referenced ps'))
        referenced' ((_, (TList (TRecord _ ps')), ms) :: xs) acc = case lookup "reference" ms of
                                                                        Just (MVString dst) => referenced' xs ((dst :: acc) ++ (referenced ps'))
                                                                        _ => referenced' xs (acc ++ (referenced ps'))
        referenced' ((_, _, ms) :: xs)                       acc = case lookup "reference" ms of
                                                                        Just (MVString dst) => referenced' xs (dst :: acc)
                                                                        _ => referenced' xs acc

    generateImports : List Name -> String
    generateImports refereds
      = List.join "\n" [ "import asyncdispatch, gateway_helper, httpbeauty, httpbeast, json, options, random, re, sequtils, sets, sonic, strtabs, strutils, times"
                       , "import redis except `%`"
                       , List.join "\n" $ map (\x => "import " ++ (toNimName x)) refereds
                       ]

    generateEventCalls : String -> String -> String -> List Parameter -> List1 Event -> String
    generateEventCalls pre name defaultMiddleware idfields es
      = let fsmidcode = generateFsmId pre name idfields in
            List1.join "\n\n" $ map (generateEvent pre name fsmidcode) es
      where
        generateFsmId : String -> String -> List Parameter -> String
        generateFsmId pre name []
          = "generate_fsmid($tenant & \"-" ++ name ++ "-\" & $now())"
        generateFsmId pre name ((n, t, ms) :: [])
          = case lookup "fsmid" ms of
                 Just (MVString "copy") => toNimName n
                 _ => "generate_fsmid($tenant & \"-" ++ name ++ "-\" & $" ++ (toNimName n) ++ ")"
        generateFsmId pre name idfields
          = "generate_fsmid($tenant & \"-" ++ name ++ "-\" & " ++ (join " & " (map (\(n, t, _) => "$" ++ (toNimName n)) idfields)) ++ ")"

        generateEvent : String -> String -> String -> Event -> String
        generateEvent pre name fsmidcode evt@(MkEvent n ps ms)
          = let style = fsmIdStyleOfEvent evt
                mw = middleware defaultMiddleware ms in
                join "\n" $ List.filter nonblank [ "proc " ++ (toNimName n) ++ "*(request: Request, ctx: GatewayContext): Future[Option[ResponseData]] {.async, gcsafe, locks:0.} ="
                                                 , if style == FsmIdStyleUrl then (indent indentDelta) ++ "var matches: array[1, string]" else ""
                                                 , if style == FsmIdStyleUrl then (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpPost and match(request.path.get(\"\"), re\"^\\/" ++ name ++ "\\/([0-9]+)\\/" ++ n ++ "$\", matches):" else (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpPost and request.path.get(\"\") == \"/" ++ name ++ "/" ++ n ++ "\":"
                                                 , generateMiddleware (indentDelta * 2) name fsmidcode n style mw ps
                                                 , (indent indentDelta) ++ "else:"
                                                 , (indent (indentDelta * 2)) ++ "result = none(ResponseData)"
                                                 ]

          where
            generateGetEventArgument : Nat -> Parameter -> String
            generateGetEventArgument idt (n, (TPrimType PTLong), _)  = let lhs = (indent idt) ++ (toNimName n)
                                                                           rhs = "data{\"" ++ n ++ "\"}.getStr(\"0\")" in
                                                                           lhs ++ " = " ++ rhs
            generateGetEventArgument idt (n, (TPrimType PTULong), _) = let lhs = (indent idt) ++ (toNimName n)
                                                                           rhs = "data{\"" ++ n ++ "\"}.getStr(\"0\")" in
                                                                           lhs ++ " = " ++ rhs
            generateGetEventArgument idt (n, (TList t), _)           = let lhs = (indent idt) ++ (toNimName n)
                                                                           rhs = "data{\"" ++ n ++ "\"}" in
                                                                           lhs ++ " = " ++ rhs
            generateGetEventArgument idt (n, (TDict k v), _)         = let lhs = (indent idt) ++ (toNimName n)
                                                                           rhs = "data{\"" ++ n ++ "\"}" in
                                                                           lhs ++ " = " ++ rhs
            generateGetEventArgument idt (n, (TRecord _ _), _)       = let lhs = (indent idt) ++ (toNimName n)
                                                                           rhs = "data{\"" ++ n ++ "\"}" in
                                                                           lhs ++ " = " ++ rhs
            generateGetEventArgument idt (n, t, _)                   = let lhs = (indent idt) ++ (toNimName n)
                                                                           rhs = toNimFromJson ("data{\"" ++ n ++ "\"}") t in
                                                                           lhs ++ " = " ++ rhs

            generateGetEventArguments : Nat -> List Parameter -> String
            generateGetEventArguments idt [] = ""
            generateGetEventArguments idt ps = List.join "\n" [ (indent idt) ++ "data = parseJson(request.body.get(\"{}\"))"
                                                              , List.join "\n" $ map (generateGetEventArgument idt) ps
                                                              ]

            generateSignatureBody : Nat -> List Parameter -> String
            generateSignatureBody idt ps
              = let items = map generateSignatureBody' $ sortBy (\(a, _, _), (b, _, _) => compare a b) ps in
                    if length items > Z
                       then (indent idt) ++ "signbody = @[" ++ (join ", " items) ++ "].join(\"&\")"
                       else (indent idt) ++ "signbody = \"\""
              where
                generateSignatureBody' : Parameter -> String
                generateSignatureBody' (n, (TPrimType PTString), _) = "\"" ++ n ++ "=\" & " ++ (toNimName n)
                generateSignatureBody' (n, (TPrimType PTLong), _)   = "\"" ++ n ++ "=\" & " ++ (toNimName n)
                generateSignatureBody' (n, (TPrimType PTULong), _)  = "\"" ++ n ++ "=\" & " ++ (toNimName n)
                generateSignatureBody' (n, (TList _), _)            = "\"" ++ n ++ "=\" & $ " ++ (toNimName n)
                generateSignatureBody' (n, (TDict _ _), _)          = "\"" ++ n ++ "=\" & $ " ++ (toNimName n)
                generateSignatureBody' (n, _,                    _) = "\"" ++ n ++ "=\" & $ " ++ (toNimName n)

            generateMainBody : Nat -> String -> String -> FsmIdStyle -> String -> List Parameter -> String
            generateMainBody idt fsmidcode n fsmIdStyle mw ps
              = let isInSession = isInfixOf "session" mw
                    idCode = case fsmIdStyle of
                                  FsmIdStyleUrl => "id.parseBiggestUInt"
                                  FsmIdStyleSession => "session"
                                  FsmIdStyleDomain => "domain"
                                  _ => fsmidcode
                    in
                    join "\n" $ List.filter nonblank [ (indent idt) ++ "let"
                                                     , (indent (idt + (indentDelta * 1))) ++ "callback = $rand(uint64)"
                                                     , (indent (idt + (indentDelta * 1))) ++ "fsmid = " ++ idCode

                                                     , (indent (idt + (indentDelta * 1))) ++ "args = {"
                                                     , (indent (idt + (indentDelta * 2))) ++ "\"TENANT\": $tenant,"
                                                     , (indent (idt + (indentDelta * 2))) ++ "\"DOMAIN\": $domain,"
                                                     , (indent (idt + (indentDelta * 2))) ++ "\"GATEWAY\": ctx.gateway,"
                                                     , (indent (idt + (indentDelta * 2))) ++ "\"TASK\": \"PLAY-EVENT\","
                                                     , (indent (idt + (indentDelta * 2))) ++ "\"FSMID\": $fsmid,"
                                                     , (indent (idt + (indentDelta * 2))) ++ "\"EVENT\": " ++ (show (toUpper n)) ++ ","
                                                     , (indent (idt + (indentDelta * 2))) ++ "\"CALLBACK\": callback,"
                                                     , (indent (idt + (indentDelta * 2))) ++ "\"OCCURRED-AT\": $to_mytimestamp(now()),"
                                                     , if isInSession then (indent (idt + (indentDelta * 2))) ++ "\"TRIGGER\": $session," else ""
                                                     , if length ps > 0 then (indent (idt + (indentDelta * 2))) ++ "\"PAYLOAD\": $data," else ""
                                                     , (indent (idt + (indentDelta * 1))) ++ "}"
                                                     , (indent idt) ++ "discard await ctx.queue_redis.xadd(queue, @args)"
                                                     , (indent idt) ++ "result = await check_result(ctx.cache_redis, tenant, callback, 0)"
                                                     ]

            generateMiddleware : Nat -> String -> String -> String -> FsmIdStyle -> String -> List Parameter -> String
            generateMiddleware idt name fsmidcode ename fsmIdStyle mw ps
              = join "\n" $ List.filter nonblank [ (indent idt) ++ "let"
                                                 , if fsmIdStyle == FsmIdStyleUrl then (indent (idt + (indentDelta * 1))) ++ "id = matches[0]" else ""
                                                 , generateGetEventArguments (idt + indentDelta) ps
                                                 , generateSignatureBody (idt + indentDelta) ps
                                                 , (indent idt) ++ "check_" ++ (toNimName mw) ++ "(request, ctx, \"POST|/" ++  (Data.List.join "/" (if fsmIdStyle == FsmIdStyleUrl then [name, "$2", ename] else [name, ename])) ++ (if fsmIdStyle == FsmIdStyleUrl then "|$1\" % [signbody, id], \"" ++ name ++ ":" ++ ename ++ "\"):" else "|\" & signbody, \"" ++ name ++ ":" ++ ename ++ "\"):")
                                                 , generateMainBody (idt + indentDelta) fsmidcode n fsmIdStyle mw ps
                                                 ]

    generateFetchObject : String -> String -> String -> Fsm -> String
    generateFetchObject pre name defaultMiddleware fsm@(MkFsm _ _ _ _ _ _ metas)
      = let mw = middleware defaultMiddleware metas
            fsmIdStyle = fsmIdStyleOfFsm fsm in
            join "\n" $ List.filter nonblank [ "proc get_" ++ (toNimName name) ++ "*(request: Request, ctx: GatewayContext): Future[Option[ResponseData]] {.async, gcsafe, locks:0.} ="
                                             , if fsmIdStyle == FsmIdStyleUrl then (indent indentDelta) ++ "var matches: array[1, string]" else ""
                                             , (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpGet and " ++ (if fsmIdStyle == FsmIdStyleUrl then "match(request.path.get(\"\"),  re\"^\\/" ++ name ++ "\\/([0-9]+)$\", matches):" else "request.path.get(\"\") == \"/" ++ name ++ "\":")
                                             , (indent (indentDelta * 2)) ++ "let"
                                             , if fsmIdStyle == FsmIdStyleUrl then (indent (indentDelta * 3)) ++ "id = matches[0]" else ""
                                             , (indent (indentDelta * 3)) ++ "signbody = \"\""
                                             , (indent (indentDelta * 2)) ++ if fsmIdStyle == FsmIdStyleSession || fsmIdStyle == FsmIdStyleDomain then ("check_signature_security_session(request, ctx, \"GET|/" ++ name ++ "|\" & signbody, \"\"):") else ("check_signature_security_session(request, ctx, \"GET|/" ++ name ++ "/$2|$1\" % [signbody, id], \"\"):")
                                             , (indent (indentDelta * 3)) ++ "let"
                                             , if fsmIdStyle == FsmIdStyleSession then (indent (indentDelta * 4)) ++ "id = $session" else ""
                                             , if fsmIdStyle == FsmIdStyleDomain then (indent (indentDelta * 4)) ++ "id = $domain" else ""
                                             , (indent (indentDelta * 4)) ++ "key = \"tenant:\" & $tenant & \"#" ++ name ++ ":\" & id"
                                             , (indent (indentDelta * 4)) ++ "objopt = await get_" ++ (toNimName name) ++ "_json(ctx.cache_redis, tenant, key)"
                                             , (indent (indentDelta * 3)) ++ "if objopt.isSome:"
                                             , (indent (indentDelta * 4)) ++ "var obj = objopt.get"
                                             , (indent (indentDelta * 4)) ++ "obj.add(\"fsmid\", %id)"
                                             , (indent (indentDelta * 4)) ++ "var ret = newJObject()"
                                             , (indent (indentDelta * 4)) ++ "ret.add(\"code\", %200)"
                                             , (indent (indentDelta * 4)) ++ "ret.add(\"payload\", obj)"
                                             , (indent (indentDelta * 4)) ++ "resp(ret)"
                                             , (indent (indentDelta * 3)) ++ "else:"
                                             , (indent (indentDelta * 4)) ++ "var ret = newJObject()"
                                             , (indent (indentDelta * 4)) ++ "ret.add(\"code\", %404)"
                                             , (indent (indentDelta * 4)) ++ "ret.add(\"payload\", %\"Not Found\")"
                                             , (indent (indentDelta * 4)) ++ "resp(ret)"
                                             , (indent indentDelta) ++ "else:"
                                             , (indent (indentDelta * 2)) ++ "result = none(ResponseData)"
                                             ]

    generateFetchLists : String -> String -> String -> List1 State -> List1 Transition -> String
    generateFetchLists pre name defaultMiddleware states transitions
      = let filteredStates = liftListStates states transitions
            listCode = map (generateFetchList pre name defaultMiddleware "" "\"tenant:\" & $tenant") filteredStates
            pairs = liftListStatesOfParticipants states transitions
            listCodeOfParticipant = map (\(s, p) => generateFetchList pre name defaultMiddleware ("-of-" ++ p) ("\"tenant:\" & $tenant & \"#" ++ p ++ ":\" & $domain") s) pairs in
            List.join "\n\n" (listCode ++ listCodeOfParticipant)
      where
        generateFetchList : String -> String -> String -> String -> String -> State -> String
        generateFetchList pre name defaultMiddleware funPostfix cachePostfix (MkState n _ _ ms)
          = let mw = middleware defaultMiddleware ms
                path = "/" ++ name ++ "/" ++ n
                nimname = toNimName name in
                join "\n" $ List.filter nonblank [ "proc get_" ++ (toNimName (n ++ "-" ++ nimname ++ "-list" ++ funPostfix)) ++ "*(request: Request, ctx: GatewayContext): Future[Option[ResponseData]] {.async, gcsafe, locks:0.} ="
                                                 , (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpGet and (request.path.get(\"\") == \"" ++ path ++ "\" or request.path.get(\"\").startsWith(\"" ++ path ++ "?\")):"
                                                 , (indent (indentDelta * 2)) ++ "let"
                                                 , (indent (indentDelta * 3)) ++ "params   = request.params"
                                                 , (indent (indentDelta * 3)) ++ "offset   = parseInt(params.getOrDefault(\"offset\", \"0\"))"
                                                 , (indent (indentDelta * 3)) ++ "limit    = parseInt(params.getOrDefault(\"limit\", \"10\"))"
                                                 , (indent (indentDelta * 3)) ++ "signbody = @[\"limit=\" & $limit, \"offset=\" & $offset].join(\"&\")"
                                                 , (indent (indentDelta * 2)) ++ "check_" ++ (toNimName mw) ++ "(request, ctx, \"GET|" ++ path ++ "|\" & signbody, \"" ++ name ++ ":get-" ++ n ++ "-list" ++ funPostfix ++ "\"):"
                                                 , (indent (indentDelta * 3)) ++ "let"
                                                 , (indent (indentDelta * 4)) ++ "srckey = " ++ cachePostfix ++ " & \"#" ++ name ++ "." ++ n ++ "\""
                                                 , (indent (indentDelta * 4)) ++ "total  = await ctx.cache_redis.zcard(srckey)"
                                                 , (indent (indentDelta * 4)) ++ "ids    = await ctx.cache_redis.zrevrange(srckey, offset, offset + limit - 1)"
                                                 , (indent (indentDelta * 3)) ++ "var items = newJArray()"
                                                 , (indent (indentDelta * 3)) ++ "for id in ids:"
                                                 , (indent (indentDelta * 4)) ++ "let"
                                                 , (indent (indentDelta * 5)) ++ "key = " ++ "\"tenant:\" & $tenant & \"#" ++ name ++ ":\" & id"
                                                 , (indent (indentDelta * 5)) ++ "itemopt = await get_" ++ nimname ++ "_json(ctx.cache_redis, tenant, key)"
                                                 , (indent (indentDelta * 4)) ++ "if " ++ "itemopt.isSome:"
                                                 , (indent (indentDelta * 5)) ++ "var item = itemopt.get"
                                                 , (indent (indentDelta * 5)) ++ "item.add(\"fsmid\", %id)"
                                                 , (indent (indentDelta * 5)) ++ "items.add(item)"
                                                 , (indent (indentDelta * 3)) ++ "var pagination = newJObject()"
                                                 , (indent (indentDelta * 3)) ++ "pagination.add(\"total\", % total)"
                                                 , (indent (indentDelta * 3)) ++ "pagination.add(\"offset\", % offset)"
                                                 , (indent (indentDelta * 3)) ++ "pagination.add(\"limit\", % limit)"
                                                 , (indent (indentDelta * 3)) ++ "var payload = newJObject()"
                                                 , (indent (indentDelta * 3)) ++ "payload.add(\"pagination\", pagination)"
                                                 , (indent (indentDelta * 3)) ++ "payload.add(\"data\", items)"
                                                 , (indent (indentDelta * 3)) ++ "var ret = newJObject()"
                                                 , (indent (indentDelta * 3)) ++ "ret.add(\"code\", %200)"
                                                 , (indent (indentDelta * 3)) ++ "ret.add(\"payload\", payload)"
                                                 , (indent (indentDelta * 3)) ++ "resp(ret)"
                                                 , (indent indentDelta) ++ "else:"
                                                 , (indent (indentDelta * 2)) ++ "result = none(ResponseData)"
                                                 ]

    generateFetchListsByReferences : String -> String -> String -> List1 State -> List1 Transition -> List Parameter -> String
    generateFetchListsByReferences pre name defaultMiddleware states transitions manyToOneFields
      = List.join "\n\n" $ map (generateFetchListsByReference pre name defaultMiddleware states transitions) manyToOneFields
      where
        generateFetchListByReference : String -> String -> String -> String -> String -> String -> State -> String
        generateFetchListByReference pre name defaultMiddleware refname funPostfix cachePostfix (MkState sname _ _ ms)
          = let mw = middleware defaultMiddleware ms
                nimname = toNimName name
                matchString = "^\/" ++ refname ++ "\/([0-9]+)\/" ++ name ++ "\/" ++ sname ++ ".*$"
                query = "/" ++ refname ++ "/$2/" ++ name ++ "/" ++ sname in
                join "\n" $ List.filter nonblank [ "proc get_" ++ (toNimName (sname ++ "-" ++ name ++ "-list" ++ funPostfix ++ "-by-" ++ refname)) ++ "*(request: Request, ctx: GatewayContext): Future[Option[ResponseData]] {.async, gcsafe, locks:0.} ="
                                                 , (indent indentDelta) ++ "var matches: array[1, string]"
                                                 , (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpGet and match(request.path.get(\"\"), re\"" ++ matchString ++ "\", matches):"
                                                 , (indent (indentDelta * 2)) ++ "let"
                                                 , (indent (indentDelta * 3)) ++ "rid      = matches[0]"
                                                 , (indent (indentDelta * 3)) ++ "params   = request.params"
                                                 , (indent (indentDelta * 3)) ++ "offset   = parseInt(params.getOrDefault(\"offset\", \"0\"))"
                                                 , (indent (indentDelta * 3)) ++ "limit    = parseInt(params.getOrDefault(\"limit\", \"10\"))"
                                                 , (indent (indentDelta * 3)) ++ "signbody = @[\"limit=\" & $limit, \"offset=\" & $offset].join(\"&\")"
                                                 , (indent (indentDelta * 2)) ++ "check_" ++ (toNimName mw) ++ "(request, ctx, \"GET|" ++ query ++ "|$1\" % [signbody, rid], \"" ++ name ++ ":get-" ++ sname ++ "-list-by-" ++ refname ++ funPostfix ++ "\"):"
                                                 , (indent (indentDelta * 3)) ++ "let"
                                                 , (indent (indentDelta * 4)) ++ "srckey = " ++ cachePostfix ++ " & \"#" ++ refname ++ ":\" & rid & \"#" ++ name ++ "." ++ sname ++ "\""
                                                 , (indent (indentDelta * 4)) ++ "total  = await ctx.cache_redis.zcard(srckey)"
                                                 , (indent (indentDelta * 4)) ++ "ids    = await ctx.cache_redis.zrevrange(srckey, offset, offset + limit - 1)"
                                                 , (indent (indentDelta * 3)) ++ "var items = newJArray()"
                                                 , (indent (indentDelta * 3)) ++ "for id in ids:"
                                                 , (indent (indentDelta * 4)) ++ "let"
                                                 , (indent (indentDelta * 5)) ++ "key = " ++ "\"tenant:\" & $tenant & \"#" ++ name ++ ":\" & id"
                                                 , (indent (indentDelta * 5)) ++ "itemopt = await get_" ++ nimname ++ "_json(ctx.cache_redis, tenant, key)"
                                                 , (indent (indentDelta * 4)) ++ "if " ++ "itemopt.isSome:"
                                                 , (indent (indentDelta * 5)) ++ "var item = itemopt.get"
                                                 , (indent (indentDelta * 5)) ++ "item.add(\"fsmid\", %id)"
                                                 , (indent (indentDelta * 5)) ++ "items.add(item)"
                                                 , (indent (indentDelta * 3)) ++ "var pagination = newJObject()"
                                                 , (indent (indentDelta * 3)) ++ "pagination.add(\"total\", % total)"
                                                 , (indent (indentDelta * 3)) ++ "pagination.add(\"offset\", % offset)"
                                                 , (indent (indentDelta * 3)) ++ "pagination.add(\"limit\", % limit)"
                                                 , (indent (indentDelta * 3)) ++ "var payload = newJObject()"
                                                 , (indent (indentDelta * 3)) ++ "payload.add(\"pagination\", pagination)"
                                                 , (indent (indentDelta * 3)) ++ "payload.add(\"data\", items)"
                                                 , (indent (indentDelta * 3)) ++ "var ret = newJObject()"
                                                 , (indent (indentDelta * 3)) ++ "ret.add(\"code\", %200)"
                                                 , (indent (indentDelta * 3)) ++ "ret.add(\"payload\", payload)"
                                                 , (indent (indentDelta * 3)) ++ "resp(ret)"
                                                 , (indent indentDelta) ++ "else:"
                                                 , (indent (indentDelta * 2)) ++ "result = none(ResponseData)"
                                                 ]

        generateFetchListsByReference : String -> String -> String -> List1 State -> List1 Transition -> Parameter -> String
        generateFetchListsByReference pre name defaultMiddleware states transitions (fname, _, metas)
          = let refname = case lookup "reference" metas of
                               Just (MVString refname') => refname'
                               _ => fname
                filteredStates = liftListStates states transitions
                listCode = map (generateFetchListByReference pre name defaultMiddleware refname "" "\"tenant:\" & $tenant") filteredStates
                pairs = liftListStatesOfParticipants states transitions
                listCodeOfParticipant = map (\(s, p) => generateFetchListByReference pre name defaultMiddleware refname ("-of-" ++ p) ("\"tenant:\" & $tenant & \"#" ++ p ++ ":\" & $session") s) pairs in
                List.join "\n\n" (listCode ++ listCodeOfParticipant)

    generateDereferenceRecordFromJsons : String -> String -> List Tipe -> String
    generateDereferenceRecordFromJsons pre name ts
      = join "\n\n" $ List.filter nonblank $ map generateDereferenceRecordFromJson ts
      where
        generateDereferenceRecordFromJson : Tipe -> String
        generateDereferenceRecordFromJson (TRecord n ps)
          = let refs = filter referenceFilter ps in
                List.join "\n" [ "proc dereference_" ++ (toNimName n) ++ "_from_json(redis: AsyncRedis, tenant: uint64, data: JsonNode): Future[JsonNode] {.async.} ="
                               , (indent indentDelta) ++ "result = data"
                               , List.join "\n" $ map (generateDereferencedAttributeOfRecord indentDelta) refs
                               ]
          where
            generateDereferencedAttributeOfRecord : Nat -> Parameter -> String
            generateDereferencedAttributeOfRecord idt (n, (TPrimType PTULong), metas)
              = let ref = case lookup "reference" metas of
                               Just (MVString r) => r
                               _ => n
                               in
                    List.join "\n" [ (indent idt) ++ "let"
                                   , (indent (idt + indentDelta)) ++ (toNimName n) ++ "_fsmid = result[\"" ++ n ++ "\"].getStr"
                                   , (indent (idt + indentDelta)) ++ (toNimName n) ++ "_key = \"tenant:\" & $tenant & \"#" ++ ref ++ ":\" & result[\"" ++ n ++ "\"].getStr"
                                   , (indent (idt + indentDelta)) ++ (toNimName n) ++ "_opt = await get_" ++ (toNimName ref) ++ "_json(redis, tenant, " ++ (toNimName n) ++ "_key)"
                                   , (indent idt) ++ "if " ++ (toNimName n) ++ "_opt.isSome:"
                                   , (indent (idt + indentDelta)) ++ "let " ++ (toNimName n) ++ "_json = " ++ (toNimName n) ++ "_opt.get"
                                   , (indent (idt + indentDelta)) ++ (toNimName n) ++ "_json.add \"fsmid\", % " ++ (toNimName n) ++ "_fsmid"
                                   , (indent (idt + indentDelta)) ++ "result[\"" ++ n ++ "\"] = " ++ (toNimName n) ++ "_opt.get"
                                   ]
            generateDereferencedAttributeOfRecord idt _
              = ""
        generateDereferenceRecordFromJson _
          = ""

    generateGetJsonCall : String -> String -> List Parameter -> String
    generateGetJsonCall pre name ps
      = let nimname = toNimName name
            (norms, refs) = splitParameters ps in
            join "\n" $ List.filter nonblank [ "proc get_" ++ nimname ++ "_json*(redis: AsyncRedis, tenant: uint64, key: string): Future[Option[JsonNode]] {.async.} ="
                                             , (indent indentDelta) ++ "let"
                                             , (indent (indentDelta * 2)) ++ "fields = @[" ++ (join ", " (map (\(n, _, _) => (show . toUpper) n) ps)) ++ "]"
                                             , (indent (indentDelta * 2)) ++ "values = await redis.hmget(key, fields)"
                                             , (indent indentDelta) ++ "var"
                                             , (indent (indentDelta * 2)) ++ "payload = newJObject()"
                                             , (indent (indentDelta * 2)) ++ "nilcount = 0"
                                             , (indent (indentDelta * 2)) ++ "idx = 0"
                                             , (indent indentDelta) ++ "for val in values:"
                                             , (indent (indentDelta * 2)) ++ "if val.isSome:"
                                             , (indent (indentDelta * 3)) ++ "case fields[idx]:"
                                             , join "\n" $ map (\(n, t, _) => generateGetJsonHandler (indentDelta * 4) n t) norms
                                             , join "\n" $ map (\((n, t, _), r) => generateGetReferenceJsonHandler (indentDelta * 4) n t r) refs
                                             , (indent (indentDelta * 4)) ++ "else:"
                                             , (indent (indentDelta * 5)) ++ "payload.add(fields[idx].toLowerAscii, % val.get)"
                                             , (indent (indentDelta * 2)) ++ "else:"
                                             , (indent (indentDelta * 3)) ++ "case fields[idx]:"
                                             , join "\n" $ map (\(n, t, _) => generateDefaultGetJsonHandler (indentDelta * 4) n t) ps
                                             , (indent (indentDelta * 4)) ++ "else:"
                                             , (indent (indentDelta * 5)) ++ "payload.add(fields[idx].toLowerAscii, % \"\")"
                                             , (indent (indentDelta * 3)) ++ "nilcount += 1"
                                             , (indent (indentDelta * 2)) ++ "idx += 1"
                                             , (indent indentDelta) ++ "if len(values) == nilcount:"
                                             , (indent (indentDelta * 2)) ++ "result = none(JsonNode)"
                                             , (indent indentDelta) ++ "else:"
                                             , (indent (indentDelta * 2)) ++ "result = some[JsonNode](payload)"
                                             ]
      where
        splitParameters : List Parameter -> (List Parameter, List (Parameter, String))
        splitParameters ps
          = splitParameters' ps [] []
          where
            splitParameters' : List Parameter -> List Parameter -> List (Parameter, String) -> (List Parameter, List (Parameter, String))
            splitParameters' []                   acc1 acc2 = (acc1, acc2)
            splitParameters' (p@(_, _, ms) :: xs) acc1 acc2 = case lookup "reference" ms of
                                                                   Just (MVString r) => splitParameters' xs acc1 ((p, r) :: acc2)
                                                                   _ => splitParameters' xs (p :: acc1) acc2

        generateGetJsonHandler : Nat -> Name -> Tipe -> String
        generateGetJsonHandler idt n (TList (TPrimType PTLong))
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "var " ++ (toNimName n) ++ "_elems: seq[string] = @[]"
                           , (indent (idt + indentDelta)) ++ "for elem in val.get.parseJson:"
                           , (indent (idt + indentDelta * 2)) ++ (toNimName n) ++ "_elems.add(elem.getStr(\"0\"))"
                           , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, %" ++ (toNimName n) ++ "_elems)"
                           ]
        generateGetJsonHandler idt n (TList (TPrimType PTULong))
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "var " ++ (toNimName n) ++ "_elems: seq[string] = @[]"
                           , (indent (idt + indentDelta)) ++ "for elem in val.get.parseJson:"
                           , (indent (idt + indentDelta * 2)) ++ (toNimName n) ++ "_elems.add(elem.getStr(\"0\"))"
                           , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, %" ++ (toNimName n) ++ "_elems)"
                           ]
        generateGetJsonHandler idt n (TList (TRecord rn ps))
          = let refs = filter referenceFilter ps in
                if length refs == 0
                   then List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                                       , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, % " ++ "val.get.parseJson)"
                                       ]
                   else List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                                       , (indent (idt + indentDelta)) ++ "var " ++ (toNimName n) ++ "_elems = newJArray()"
                                       , (indent (idt + indentDelta)) ++ "for elem in val.get.parseJson:"
                                       , (indent (idt + indentDelta * 2)) ++ (toNimName n) ++ "_elems.add(await dereference_" ++ (toNimName rn) ++ "_from_json(redis, tenant, elem))"
                                       , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, %" ++ (toNimName n) ++ "_elems)"
                                       ]
        generateGetJsonHandler idt n (TList _)
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, val.get.parseJson)"
                           ]
        generateGetJsonHandler idt n (TDict _ (TPrimType PTLong))
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "var " ++ (toNimName n) ++ "_elems: StringTableRef = newStringTable()"
                           , (indent (idt + indentDelta)) ++ "var " ++ (toNimName n) ++ "_vals = val.get.parseJson"
                           , (indent (idt + indentDelta)) ++ "for key in " ++ (toNimName n) ++ "_vals:"
                           , (indent (idt + indentDelta * 2)) ++ (toNimName n) ++ "_elems[key] = $" ++ (toNimName n) ++ "_vals[key].getStr(\"0\").parseBiggestInt"
                           , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, " ++ (toNimName n) ++ "_elems)"
                           ]
        generateGetJsonHandler idt n (TDict _ (TPrimType PTULong))
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "var " ++ (toNimName n) ++ "_elems: StringTableRef = newStringTable()"
                           , (indent (idt + indentDelta)) ++ "var " ++ (toNimName n) ++ "_vals = val.get.parseJson"
                           , (indent (idt + indentDelta)) ++ "for key in " ++ (toNimName n) ++ "_vals:"
                           , (indent (idt + indentDelta * 2)) ++ (toNimName n) ++ "_elems[key] = $" ++ (toNimName n) ++ "_vals[key].getStr(\"0\").parseBiggestInt"
                           , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, " ++ (toNimName n) ++ "_elems)"
                           ]
        generateGetJsonHandler idt n (TDict _ _)
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, val.get.parseJson)"
                           ]
        generateGetJsonHandler idt n (TRecord _ _)
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, val.get.parseJson)"
                           ]
        generateGetJsonHandler idt n (TPrimType PTLong)
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, % " ++ "val.get(\"0\"))"
                           ]
        generateGetJsonHandler idt n (TPrimType PTULong)
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, % " ++ "val.get(\"0\"))"
                           ]
        generateGetJsonHandler idt n t
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, % " ++ (toNimFromString "val.get" t) ++ ")"
                           ]

        generateGetReferenceJsonHandler : Nat -> Name -> Tipe -> String -> String
        generateGetReferenceJsonHandler idt n (TList (TPrimType PTLong)) ref
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "var " ++ (toNimName n) ++ "_elems = newJArray()"
                           , (indent (idt + indentDelta)) ++ "for elem in val.get.parseJson:"
                           , (indent (idt + indentDelta * 2)) ++ "let"
                           , (indent (idt + indentDelta * 3)) ++ "key = \"tenant:\" & $tenant & \"#" ++ ref ++ ":\" & elem.getStr(\"0\")"
                           , (indent (idt + indentDelta * 3)) ++ (toNimName n) ++ "_opt" ++ " = await get_" ++ (toNimName ref) ++ "_json(redis, tenant, key)"
                           , (indent (idt + indentDelta * 2)) ++ "if " ++ (toNimName n) ++ "_opt.isSome:"
                           , (indent (idt + indentDelta * 3)) ++ "let " ++ (toNimName n) ++ " = " ++ (toNimName n) ++ "_opt.get"
                           , (indent (idt + indentDelta * 3)) ++ (toNimName n) ++ ".add(\"fsmid\", elem)"
                           , (indent (idt + indentDelta * 3)) ++ (toNimName n) ++ "_elems.add(" ++ (toNimName n) ++ ")"
                           , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, " ++ (toNimName n) ++ "_elems)"
                           ]
        generateGetReferenceJsonHandler idt n (TList (TPrimType PTULong)) ref
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "var " ++ (toNimName n) ++ "_elems = newJArray()"
                           , (indent (idt + indentDelta)) ++ "for elem in val.get.parseJson:"
                           , (indent (idt + indentDelta * 2)) ++ "let"
                           , (indent (idt + indentDelta * 3)) ++ "key = \"tenant:\" & $tenant & \"#" ++ ref ++ ":\" & elem.getStr(\"0\")"
                           , (indent (idt + indentDelta * 3)) ++ (toNimName n) ++ "_opt" ++ " = await get_" ++ (toNimName ref) ++ "_json(redis, tenant, key)"
                           , (indent (idt + indentDelta * 2)) ++ "if " ++ (toNimName n) ++ "_opt.isSome:"
                           , (indent (idt + indentDelta * 3)) ++ "let " ++ (toNimName n) ++ " = " ++ (toNimName n) ++ "_opt.get"
                           , (indent (idt + indentDelta * 3)) ++ (toNimName n) ++ ".add(\"fsmid\", elem)"
                           , (indent (idt + indentDelta * 3)) ++ (toNimName n) ++ "_elems.add(" ++ (toNimName n) ++ ")"
                           , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, " ++ (toNimName n) ++ "_elems)"
                           ]
        generateGetReferenceJsonHandler idt n _ ref
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "let"
                           , (indent (idt + indentDelta * 2)) ++ "key = \"tenant:\" & $tenant & \"#" ++ ref ++ ":\" & val.get(\"0\")"
                           , (indent (idt + indentDelta * 2)) ++ (toNimName n) ++ "_opt" ++ " = await get_" ++ (toNimName ref) ++ "_json(redis, tenant, key)"
                           , (indent (idt + indentDelta)) ++ "if " ++ (toNimName n) ++ "_opt.isSome:"
                           , (indent (idt + indentDelta * 2)) ++ "let " ++ (toNimName n) ++ " = " ++ (toNimName n) ++ "_opt.get"
                           , (indent (idt + indentDelta * 2)) ++ (toNimName n) ++ ".add(\"fsmid\", % val.get)"
                           , (indent (idt + indentDelta * 2)) ++ "payload.add(fields[idx].toLowerAscii, " ++ (toNimName n) ++ ")"
                           , (indent (idt + indentDelta)) ++ "else:"
                           , (indent (idt + indentDelta * 2)) ++ "payload.add(fields[idx].toLowerAscii, % val.get)"
                           ]

        defaultValue : Tipe -> String
        defaultValue (TPrimType PTBool)   = "false"
        defaultValue (TPrimType PTByte)   = "0'u8"
        defaultValue (TPrimType PTChar)   = "'\\0'"
        defaultValue (TPrimType PTShort)  = "0'i16"
        defaultValue (TPrimType PTUShort) = "0'u16"
        defaultValue (TPrimType PTInt)    = "0"
        defaultValue (TPrimType PTUInt)   = "0'u32"
        defaultValue (TPrimType PTLong)   = "\"0\""
        defaultValue (TPrimType PTULong)  = "\"0\""
        defaultValue (TPrimType PTReal)   = "0.0"
        defaultValue (TPrimType PTString) = "\"\""
        defaultValue (TList _)            = "@[]"
        defaultValue _                    = "nil"

        generateDefaultGetJsonHandler : Nat -> Name -> Tipe -> String
        generateDefaultGetJsonHandler idt n t@(TDict _ _)
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, json.`%` " ++ (defaultValue t) ++ ")"
                           ]
        generateDefaultGetJsonHandler idt n (TRecord _ _)
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, newJNull())"
                           ]
        generateDefaultGetJsonHandler idt n t
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, % " ++ (defaultValue t) ++ ")"
                           ]

    generateSearch : String -> String -> String -> String -> String -> String -> String
    generateSearch pre name middleware funNamePostfix pathPostfix bucket
      = let path = "/" ++ name ++ "/search" ++ pathPostfix in
            List.join "\n" [ "proc search_" ++ (toNimName name) ++ (toNimName funNamePostfix) ++ "*(request: Request, ctx: GatewayContext): Future[Option[ResponseData]] {.async, gcsafe, locks:0.} ="
                           , (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpPost and request.path.get(\"\") == \"" ++ path ++ "\":"
                           , (indent (indentDelta * 2)) ++ "let"
                           , (indent (indentDelta * 3)) ++ "data = parseJson(request.body.get(\"{}\"))"
                           , (indent (indentDelta * 3)) ++ "offset = data{\"offset\"}.getInt"
                           , (indent (indentDelta * 3)) ++ "limit = data{\"limit\"}.getInt"
                           , (indent (indentDelta * 3)) ++ "signbody = @[\"limit=\" & $limit, \"offset=\" & $offset, \"words=\" & $ data{\"words\"}].join(\"&\")"
                           , (indent (indentDelta * 2)) ++ "check_" ++ (toNimName middleware) ++ "(request, ctx, \"POST|" ++ path ++ "|\" & signbody, \"" ++ name ++ ":search-" ++ name ++ funNamePostfix ++ "\"):"
                           , (indent (indentDelta * 3)) ++ "let sonic = await openAsync(ctx.metas.getOrDefault(\"sonic-host\"), ctx.metas.getOrDefault(\"sonic-port\").parseInt, ctx.metas.getOrDefault(\"sonic-passwd\"), SonicChannel.Search)"
                           , (indent (indentDelta * 3)) ++ "var idsets: seq[HashSet[string]] = @[]"
                           , (indent (indentDelta * 3)) ++ "for key in data{\"words\"}.keys():"
                           , (indent (indentDelta * 4)) ++ "var"
                           , (indent (indentDelta * 5)) ++ "myoffset = 0"
                           , (indent (indentDelta * 5)) ++ "ids: seq[string] = @[]"
                           , (indent (indentDelta * 4)) ++ "while true:"
                           , (indent (indentDelta * 5)) ++ "let idsfut = sonic.query(\"" ++ name ++ "\", " ++ bucket ++ ", data{\"words\"}[key].getStr, offset = myoffset, limit = 100)"
                           , (indent (indentDelta * 5)) ++ "while not idsfut.finished:"
                           , (indent (indentDelta * 6)) ++ "discard await sonic.ping"
                           , (indent (indentDelta * 5)) ++ "let tmpids = idsfut.read"
                           , (indent (indentDelta * 5)) ++ "ids = concat(ids, tmpids)"
                           , (indent (indentDelta * 5)) ++ "if len(tmpids) != 100:"
                           , (indent (indentDelta * 6)) ++ "break"
                           , (indent (indentDelta * 5)) ++ "else:"
                           , (indent (indentDelta * 6)) ++ "myoffset += 100"
                           , (indent (indentDelta * 4)) ++ "idsets.add(ids.toHashSet)"
                           , (indent (indentDelta * 3)) ++ "asyncCheck sonic.quit"
                           , (indent (indentDelta * 3)) ++ "let"
                           , (indent (indentDelta * 4)) ++ "ids = idsets.foldl(intersection(a, b))"
                           , (indent (indentDelta * 4)) ++ "total = card(ids)"
                           , (indent (indentDelta * 3)) ++ "var objs = newJArray()"
                           , (indent (indentDelta * 3)) ++ "if offset < total:"
                           , (indent (indentDelta * 4)) ++ "var idx = 0"
                           , (indent (indentDelta * 4)) ++ "for idstr in ids:"
                           , (indent (indentDelta * 5)) ++ "if idx < offset:"
                           , (indent (indentDelta * 6)) ++ "idx += 1"
                           , (indent (indentDelta * 6)) ++ "continue"
                           , (indent (indentDelta * 5)) ++ "if idx > min(offset + limit, total):"
                           , (indent (indentDelta * 6)) ++ "break"
                           , (indent (indentDelta * 5)) ++ "let"
                           , (indent (indentDelta * 6)) ++ "key = \"tenant:\" & $tenant & \"#" ++ name ++ ":\" & idstr"
                           , (indent (indentDelta * 6)) ++ "objopt = await get_" ++ (toNimName name) ++ "_json(ctx.cache_redis, tenant, key)"
                           , (indent (indentDelta * 5)) ++ "if objopt.isSome:"
                           , (indent (indentDelta * 6)) ++ "var obj = objopt.get"
                           , (indent (indentDelta * 6)) ++ "obj.add \"fsmid\", % idstr"
                           , (indent (indentDelta * 6)) ++ "objs.add obj"
                           , (indent (indentDelta * 5)) ++ "idx += 1"
                           , (indent (indentDelta * 3)) ++ "var pagination = newJObject()"
                           , (indent (indentDelta * 3)) ++ "pagination.add \"total\", % total"
                           , (indent (indentDelta * 3)) ++ "pagination.add \"offset\", % offset"
                           , (indent (indentDelta * 3)) ++ "pagination.add \"limit\", % limit"
                           , (indent (indentDelta * 3)) ++ "var payload = newJObject()"
                           , (indent (indentDelta * 3)) ++ "payload.add \"pagination\", pagination"
                           , (indent (indentDelta * 3)) ++ "payload.add \"data\", objs"
                           , (indent (indentDelta * 3)) ++ "var ret = newJObject()"
                           , (indent (indentDelta * 3)) ++ "ret.add \"code\", %200"
                           , (indent (indentDelta * 3)) ++ "ret.add \"payload\", payload"
                           , (indent (indentDelta * 3)) ++ "resp ret"
                           , (indent indentDelta) ++ "else:"
                           , (indent (indentDelta * 2)) ++ "result = none(ResponseData)"
                           ]

    generateStateSearchs : String -> String -> String -> List1 State -> List1 Transition -> String
    generateStateSearchs pre name middleware states transitions
      = let filteredStates = liftIndexStates states transitions
            indexCode = map (\(MkState sname _ _ _) => generateSearch pre name middleware ("-in-" ++ sname ++ "-state") ("/" ++ sname) ("\"state:" ++ sname ++ "&field:\" & key")) filteredStates
            pairs = liftIndexStatesOfParticipants states transitions
            indexCodeOfParticipants = map (\((MkState sname _ _ _), pname) => generateSearch pre name middleware ("-in-" ++ sname ++ "-state-of-" ++ pname) ("/" ++ sname) ("\"" ++ pname ++ ":\" & $domain & " ++ "\"&state:" ++ sname ++ "&field:\" & key")) pairs in
            List.join "\n\n" (indexCode ++ indexCodeOfParticipants)

    generateRouters : String -> String -> List1 State -> List1 Transition -> List1 Participant -> List Parameter -> Bool -> String
    generateRouters pre name ss ts ps fields searchable
      = List1.join "\n\n" $ map (generateRoutersOfParticipant pre name ss ts fields searchable) ps
      where
        generateListRouters : Nat -> String -> String -> List1 State -> List1 Transition -> List String
        generateListRouters idt pre name states transitions
          = let filteredStates = liftListStates states transitions in
                map (generateListRouter idt pre name) filteredStates
          where
            generateListRouter : Nat -> String -> String -> State -> String
            generateListRouter idt pre name (MkState sname _ _ _)
              = (indent idt) ++ "RouteProc[GatewayContext](" ++ (toNimName (name ++ ".get-" ++ sname ++ "-" ++ name ++ "-list")) ++ ")"

        generateListRoutersOfParticipant : Nat -> String -> String -> List1 State -> List1 Transition -> Participant -> List String
        generateListRoutersOfParticipant idt pre name states transitions (MkParticipant pname _)
          = let pairs = liftListStatesOfParticipants states transitions
                filtered = map (\(s, _) => s) $ filter (\(s, p) => p == pname) pairs in
                map (generateListRouterOfParticipant idt pre name pname) filtered
          where
            generateListRouterOfParticipant : Nat -> String -> String -> String -> State -> String
            generateListRouterOfParticipant idt pre name pname (MkState sname _ _ _)
              = (indent idt) ++ "RouteProc[GatewayContext](" ++ (toNimName (name ++ ".get-" ++ sname ++ "-" ++ name ++ "-list-of-" ++ pname)) ++ ")"

        generateListRoutersByReference : Nat -> String -> String -> Parameter -> List1 State -> List1 Transition -> List String
        generateListRoutersByReference idt pre name (fname, _, metas) states transitions
          = let refname = case lookup "reference" metas of
                               Just (MVString refname') => refname'
                               _ => fname
                filteredStates = liftListStates states transitions in
                map (generateListRouter idt pre name refname) filteredStates
          where
            generateListRouter : Nat -> String -> String -> String -> State -> String
            generateListRouter idt pre name refname (MkState sname _ _ _)
              = (indent idt) ++ "RouteProc[GatewayContext](" ++ (toNimName (name ++ ".get-" ++ sname ++ "-" ++ name ++ "-list-by-" ++ refname)) ++ ")"

        generateListRoutersOfParticipantByReference : Nat -> String -> String -> Parameter -> List1 State -> List1 Transition -> Participant -> List String
        generateListRoutersOfParticipantByReference idt pre name (fname, _, metas) states transitions (MkParticipant pname _)
          = let refname = case lookup "reference" metas of
                               Just (MVString refname') => refname'
                               _ => fname
                pairs = liftListStatesOfParticipants states transitions
                filtered = map (\(s, _) => s) $ filter (\(s, p) => p == pname) pairs in
                map (generateListRouterOfParticipant idt pre name refname pname) filtered
          where
            generateListRouterOfParticipant : Nat -> String -> String -> String -> String -> State -> String
            generateListRouterOfParticipant idt pre name refname pname (MkState sname _ _ _)
              = (indent idt) ++ "RouteProc[GatewayContext](" ++ (toNimName (name ++ ".get-" ++ sname ++ "-" ++ name ++ "-list-of-" ++ pname ++ "-by-" ++ refname)) ++ ")"

        generateEventRoutersByParticipantAndTransition : Nat -> String -> Participant -> Transition -> List String
        generateEventRoutersByParticipantAndTransition idt name p (MkTransition _ _ ts)
          = filter nonblank $ map (generateEventCallByParticipantAndTrigger idt name p) ts
          where
            generateEventCallByParticipantAndTrigger : Nat -> String -> Participant -> Trigger -> String
            generateEventCallByParticipantAndTrigger idt name p (MkTrigger ps e _ _)
              = if elemBy (==) p ps
                   then (indent idt) ++ "RouteProc[GatewayContext](" ++ (toNimName name) ++ "." ++ (toNimName (Event.name e)) ++ ")"
                   else ""

        generateIndexRouters : Nat -> String -> String -> List1 State -> List1 Transition -> List String
        generateIndexRouters idt pre name states transitions
          = let filteredStates = liftIndexStates states transitions in
                map (generateIndexRouter idt pre name) filteredStates
          where
            generateIndexRouter : Nat -> String -> String -> State -> String
            generateIndexRouter idt pre name (MkState sname _ _ _)
              = (indent idt) ++ "RouteProc[GatewayContext](" ++ (toNimName (name ++ ".search-" ++ name ++ "-in-" ++ sname ++ "-state")) ++ ")"

        generateIndexRoutersOfParticipant : Nat -> String -> String -> List1 State -> List1 Transition -> Participant -> List String
        generateIndexRoutersOfParticipant idt pre name states transitions (MkParticipant pname _)
          = let pairs = liftIndexStatesOfParticipants states transitions
                filtered = map (\(s, _) => s) $ filter (\(s, p) => p == pname) pairs in
                map (generateIndexRouterOfParticipant idt pre name pname) filtered
          where
            generateIndexRouterOfParticipant : Nat -> String -> String -> String -> State -> String
            generateIndexRouterOfParticipant idt pre name pname (MkState sname _ _ _)
              = (indent idt) ++ "RouteProc[GatewayContext](" ++ (toNimName (name ++ ".search-" ++ name ++ "-in-" ++ sname ++ "-state-of-" ++ pname)) ++ ")"

        generateRoutersOfParticipant : String -> String -> List1 State -> List1 Transition -> List Parameter -> Bool -> Participant -> String
        generateRoutersOfParticipant pre name ss ts fields searchable p@(MkParticipant n _)
          = let eventRouters = nub $ flatten $ List1.toList $ map (generateEventRoutersByParticipantAndTransition indentDelta name p) ts
                listRouters = generateListRouters indentDelta pre name ss ts
                listRoutersOfParticipant = generateListRoutersOfParticipant indentDelta pre name ss ts p
                referencedListRouters = flatten $ map (\field => generateListRoutersByReference indentDelta pre name field ss ts) fields
                referencedListRoutersOfParticipant = flatten $ map (\field => generateListRoutersOfParticipantByReference indentDelta pre name field ss ts p) fields
                getObjRouter = (indent indentDelta) ++ "RouteProc[GatewayContext](" ++ (toNimName name) ++ ".get_" ++ (toNimName name) ++ ")"
                indexRouters = generateIndexRouters indentDelta pre name ss ts
                indexRoutersOfParticipant = generateIndexRoutersOfParticipant indentDelta pre name ss ts p in
                List.join "\n" [ "let " ++ (toNimName n) ++ "_routers*: seq[RouteProc[GatewayContext]] = @["
                               , List.join ",\n" ( eventRouters
                                                 ++ (if length listRoutersOfParticipant > 0
                                                        then listRoutersOfParticipant
                                                        else listRouters)
                                                 ++ (if length referencedListRoutersOfParticipant > 0
                                                        then referencedListRoutersOfParticipant
                                                        else referencedListRouters)
                                                 ++ [getObjRouter]
                                                 ++ (if searchable
                                                        then (if length indexRoutersOfParticipant > 0
                                                                 then indexRoutersOfParticipant
                                                                 else indexRouters)
                                                        else [])
                                                 )
                               , "]"
                               ]

    generatePermissions : String -> String -> String -> List1 State -> List1 Transition -> List1 Participant -> List Parameter -> Bool -> String
    generatePermissions pre name display states transitions participants fields searchable
      = List1.join "\n\n" $ map (generatePermissionsOfParticipant pre name states transitions fields) participants
      where
        generateEventPermissions : Nat -> String -> Participant -> Transition -> List String
        generateEventPermissions idt name p (MkTransition _ _ ts)
          = filter nonblank $ map (generateEventPermissionsByTrigger idt name p) ts
          where
            generateEventPermissionsByTrigger : Nat -> String -> Participant -> Trigger -> String
            generateEventPermissionsByTrigger idt name p (MkTrigger ps (MkEvent ename _ metas) _ _)
              = if elemBy (==) p ps
                   then (indent idt) ++ "(\"" ++ (displayName ename metas) ++ "\", " ++ (show (name ++ ":" ++ ename)) ++ ")"
                   else ""

        generateListPermissions : Nat -> String -> String -> List1 State -> List1 Transition -> List String
        generateListPermissions idt pre name states transitions
          = let filteredStates = liftListStates states transitions in
                map (generateListPermission idt pre name) filteredStates
          where
            generateListPermission : Nat -> String -> String -> State -> String
            generateListPermission idt pre name (MkState sname _ _ smetas)
              = (indent idt) ++ "(\"" ++ "获取" ++ (displayName sname smetas) ++ "列表" ++ "\", " ++ (show (name ++ ":get-" ++ sname ++ "-list")) ++ ")"

        generateListPermissionsOfParticipant : Nat -> String -> String -> List1 State -> List1 Transition -> Participant -> List String
        generateListPermissionsOfParticipant idt pre name states transitions (MkParticipant pname _)
          = let pairs = liftListStatesOfParticipants states transitions
                filtered = map (\(s, _) => s) $ filter (\(s, p) => p == pname) pairs in
                map (generateListPermissionOfParticipant idt pre name pname) filtered
          where
            generateListPermissionOfParticipant : Nat -> String -> String -> String -> State -> String
            generateListPermissionOfParticipant idt pre name pname (MkState sname _ _ smetas)
              = (indent idt) ++ "(\"" ++ "获取" ++ (displayName sname smetas) ++ "列表" ++ "\", " ++ (show (name ++ ":get-" ++ sname ++ "-list-of-" ++ pname)) ++ ")"

        generateListPermissionsByReference : Nat -> String -> String -> Parameter -> List1 State -> List1 Transition -> List String
        generateListPermissionsByReference idt pre name (fname, _, metas) states transitions
          = let refname = case lookup "reference" metas of
                               Just (MVString refname') => refname'
                               _ => fname
                filteredStates = liftListStates states transitions in
                map (generateListPermission idt pre name refname metas) filteredStates
          where
            generateListPermission : Nat -> String -> String -> String -> Maybe (List Meta) -> State -> String
            generateListPermission idt pre name refname fmetas (MkState sname _ _ smetas)
              = (indent idt) ++ "(\"根据" ++ (displayName refname fmetas) ++ "获取" ++ (displayName sname smetas) ++ "列表" ++ "\", " ++ (show (name ++ ":get-" ++ sname ++ "-list-by-" ++ refname)) ++ ")"

        generateListPermissionsOfParticipantByReference : Nat -> String -> String -> Parameter -> List1 State -> List1 Transition -> Participant -> List String
        generateListPermissionsOfParticipantByReference idt pre name (fname, _, metas) states transitions (MkParticipant pname _)
          = let refname = case lookup "reference" metas of
                               Just (MVString refname') => refname'
                               _ => fname
                pairs = liftListStatesOfParticipants states transitions
                filtered = map (\(s, _) => s) $ filter (\(s, p) => p == pname) pairs in
                map (generateListPermissionOfParticipant idt pre name refname metas pname) filtered
          where
            generateListPermissionOfParticipant : Nat -> String -> String -> String -> Maybe (List Meta) -> String -> State -> String
            generateListPermissionOfParticipant idt pre name refname fmetas pname (MkState sname _ _ smetas)
              = (indent idt) ++ "(\"根据" ++ (displayName refname fmetas) ++ "获取" ++ (displayName sname smetas) ++ "列表" ++ "\", " ++ (show (name ++ ":get-" ++ sname ++ "-list-of-" ++ pname ++ "-by-" ++ refname)) ++ ")"

        generateIndexPermissions : Nat -> String -> String -> List1 State -> List1 Transition -> List String
        generateIndexPermissions idt pre name states transitions
          = let filteredStates = liftIndexStates states transitions in
                map (generateIndexPermission idt pre name) filteredStates
          where
            generateIndexPermission : Nat -> String -> String -> State -> String
            generateIndexPermission idt pre name (MkState sname _ _ smetas)
              = (indent idt) ++ "(\"在" ++ (displayName sname smetas) ++ "列表中搜索\", " ++ (show (name ++ ":search-" ++ name ++ "-in-" ++ sname)) ++ ")"

        generateIndexPermissionsOfParticipant : Nat -> String -> String -> List1 State -> List1 Transition -> Participant -> List String
        generateIndexPermissionsOfParticipant idt pre name states transitions (MkParticipant pname _)
          = let pairs = liftIndexStatesOfParticipants states transitions
                filtered = map (\(s, _) => s) $ filter (\(s, p) => p == pname) pairs in
                map (generateIndexPermissionOfParticipant idt pre name pname) filtered
          where
            generateIndexPermissionOfParticipant : Nat -> String -> String -> String -> State -> String
            generateIndexPermissionOfParticipant idt pre name pname (MkState sname _ _ smetas)
              = (indent idt) ++ "(\"在" ++ (displayName sname smetas) ++ "列表中搜索\", " ++ (show (name ++ ":search-" ++ name ++ "-in-" ++ sname ++ "-of-" ++ pname)) ++ ")"

        generatePermissionsOfParticipant : String -> String -> List1 State -> List1 Transition -> List Parameter -> Participant -> String
        generatePermissionsOfParticipant pre name ss ts fields p@(MkParticipant n _)
          = let eventPermissions = nub $ flatten $ List1.toList $ map (generateEventPermissions indentDelta name p) ts
                listPermissions = generateListPermissions indentDelta pre name ss ts
                listPermissionsOfParticipant = generateListPermissionsOfParticipant indentDelta pre name ss ts p
                referencedListPermissions = flatten $ map (\field => generateListPermissionsByReference indentDelta pre name field ss ts) fields
                referencedListPermissionsOfParticipant = flatten $ map (\field => generateListPermissionsOfParticipantByReference indentDelta pre name field ss ts p) fields
                indexPermissions = generateIndexPermissions indentDelta pre name ss ts
                indexPermissionsOfParticipant = generateIndexPermissionsOfParticipant indentDelta pre name ss ts p in
                List.join "\n" [ "let " ++ (toNimName n) ++ "_permissions*: seq[(string, string)] = @["
                               , List.join ",\n" ( eventPermissions
                                                 ++ (if length listPermissionsOfParticipant > 0
                                                        then listPermissionsOfParticipant
                                                        else listPermissions)
                                                 ++ (if length referencedListPermissionsOfParticipant > 0
                                                        then referencedListPermissionsOfParticipant
                                                        else referencedListPermissions)
                                                 ++ (if searchable
                                                        then (if length indexPermissionsOfParticipant > 0
                                                                 then indexPermissionsOfParticipant
                                                                 else indexPermissions)
                                                        else [])
                                                 )
                               , "]"
                               ]

loadFsm : String -> Either String Fsm
loadFsm src
  = do (sexp, _) <- mapError parseErrorToString $ parseSExp src
       (fsm, _) <- mapError parseErrorToString $ analyse sexp
       fsm' <- mapError checkersErrorToString $ check fsm defaultCheckingRules
       pure fsm'

doWork : AppConfig -> IO ()
doWork conf
  = do Right fsm <- loadFsmFromFile conf.src
       | Left err => putStrLn $ show err
       putStrLn $ toNim conf fsm

parseArgs : List String -> Maybe AppConfig
parseArgs
  = parseArgs' Nothing Nothing
  where
    parseArgs' : Maybe String -> Maybe String -> List String -> Maybe AppConfig
    parseArgs' Nothing    _                 []                 = Nothing
    parseArgs' (Just src) Nothing           []                 = Just (MkAppConfig src "signature-security-session")
    parseArgs' (Just src) (Just middleware) []                 = Just (MkAppConfig src middleware)
    parseArgs' _          _                 []                 = Nothing
    parseArgs' src        _                 ("-mw" :: x :: xs) = parseArgs' src (Just x) xs
    parseArgs' _          middleware        (x :: xs)          = parseArgs' (Just x) middleware xs

usage : String
usage
  = List.join "\n" [ "Usage: pfsm-to-nim-gateway [options] <src>"
                   , ""
                   , "Options:"
                   , "  -mv <middleware> Specify the default middleware to handle incoming requests."
                   , "                   Middlewares are:"
                   , "                   1. signature-security"
                   , "                   2. signature-security-session (default)"
                   , "                   3. signature-security-session-permission"
                   ]

main : IO ()
main
  = do args <- getArgs
       case tail' args of
            Nothing => putStrLn usage
            Just args' => case parseArgs args' of
                               Just conf => doWork conf
                               Nothing => putStrLn usage
