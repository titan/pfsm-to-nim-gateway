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

indentDelta : Nat
indentDelta = 2

toNim : Fsm -> String
toNim fsm
  = let name = fsm.name
        pre = camelize (toNimName name)
        idfields = filter idFieldFilter fsm.model
        refereds = referenced fsm.model in
        List.join "\n\n" [ generateImports refereds
                         , "const queue = " ++ (show (name ++ "-input"))
                         , generateEventCalls pre name idfields fsm.events
                         , generateGetJsonCall pre name fsm.model
                         , generateFetchObject pre name
                         , generateFetchLists pre name fsm.states
                         , generateParticipants pre name fsm.states fsm.transitions fsm.participants
                         ]
  where
    idFieldFilter : Parameter -> Bool
    idFieldFilter (_, _, ms) = case lookup "fsmid" ms of
                                    Just (MVString "true") => True
                                    _ => False

    referenced: List Parameter -> List Name
    referenced ps
      = referenced' ps []
      where
        referenced' : List Parameter -> List Name -> List Name
        referenced' []                 acc = acc
        referenced' ((_, _, ms) :: xs) acc = case lookup "reference" ms of
                                                  Just (MVString dst) => referenced' xs (dst :: acc)
                                                  _ => referenced' xs acc

    generateImports : List Name -> String
    generateImports refereds
      = List.join "\n" [ "import asyncdispatch, gateway_helper, httpbeauty, httpbeast, json, options, random, re, sequtils, strtabs, strutils, times"
                       , "import redis except `%`"
                       , List.join "\n" $ map (\x => "import " ++ (toNimName x)) refereds
                       ]

    generateEventCalls : String -> String -> List Parameter -> List1 Event -> String
    generateEventCalls pre name idfields es
      = let fsmidcode = "generate_fsmid($tenant & \"-" ++ name ++ "-\" & " ++ (join " & " (map (\(n, t, _) => "$" ++ (toNimName n)) idfields)) ++ ")" in
            List1.join "\n\n" $ map (generateEvent pre name fsmidcode) es
      where
        generateEvent : String -> String -> String -> Event -> String
        generateEvent pre name fsmidcode evt@(MkEvent n ps ms)
          = let style = fsmIdStyleOfEvent evt
                middleware = fromMaybe (MVString "signature-security-session") $ lookup "gateway.middleware" ms in
                join "\n" $ List.filter nonblank [ "proc " ++ (toNimName n) ++ "*(request: Request, ctx: GatewayContext): Future[Option[ResponseData]] {.async, gcsafe, locks:0.} ="
                                                 , if style == FsmIdStyleUrl then (indent indentDelta) ++ "var matches: array[1, string]" else ""
                                                 , if style == FsmIdStyleUrl then (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpPost and match(request.path.get(\"\"), re\"^\\/" ++ name ++ "\\/(.+)\\/" ++ n ++ "$\", matches):" else (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpPost and request.path.get(\"\") == \"/" ++ name ++ "/" ++ n ++ "\":"
                                                 , generateMiddleware (indentDelta * 2) name fsmidcode n style middleware ps
                                                 , (indent indentDelta) ++ "else:"
                                                 , (indent (indentDelta * 2)) ++ "result = none(ResponseData)"
                                                 ]

          where
            generateGetEventArgument : Nat -> Parameter -> String
            generateGetEventArgument idt (n, (TList t), _)   = let lhs = (indent idt) ++ (toNimName n)
                                                                   rhs = "data{\"" ++ n ++ "\"}" in
                                                                   lhs ++ " = " ++ rhs
            generateGetEventArgument idt (n, (TDict k v), _) = let lhs = (indent idt) ++ (toNimName n)
                                                                   rhs = "data{\"" ++ n ++ "\"}" in
                                                                   lhs ++ " = " ++ rhs
            generateGetEventArgument idt (n, t, _)           = let lhs = (indent idt) ++ (toNimName n)
                                                                   rhs = toNimFromJson ("data{\"" ++ n ++ "\"}") t in
                                                                   lhs ++ " = " ++ rhs

            generateGetEventArguments : Nat -> List Parameter -> String
            generateGetEventArguments idt [] = ""
            generateGetEventArguments idt ps = List.join "\n" [ (indent idt) ++ "data = parseJson(request.body.get(\"{}\"))"
                                                              , List.join "\n" $ map (generateGetEventArgument idt) ps
                                                              ]

            toNimArg : Name -> Tipe -> String
            toNimArg n (TPrimType PTString) = toNimName n
            toNimArg n (TPrimType _)        = "$" ++ (toNimName n)
            toNimArg n (TList t)            = "$" ++ (toNimName n)
            toNimArg n (TDict k v)          = "$" ++ (toNimName n)
            toNimArg n _                    = toNimName n

            generateEventArgument : Nat -> Parameter -> String
            generateEventArgument idt (n, t, _)
              = (indent idt) ++ (show (toUpper n)) ++ ": " ++ toNimArg (toNimName n) t ++ ","

            generateEventArguments : Nat -> List Parameter -> String
            generateEventArguments idt ps
              = List.join "\n" $ map (generateEventArgument idt) ps

            generateSignatureBody : Nat -> List Parameter -> String
            generateSignatureBody idt ps
              = let items = map generateSignatureBody' $ sortBy (\(a, _, _), (b, _, _) => compare a b) ps in
                    if length items > Z
                       then (indent idt) ++ "signbody = @[" ++ (join ", " items) ++ "].join(\"&\")"
                       else (indent idt) ++ "signbody = \"\""
              where
                generateSignatureBody' : Parameter -> String
                generateSignatureBody' (n, (TPrimType PTString), _) = "\"" ++ n ++ "=\" & " ++ (toNimName n)
                generateSignatureBody' (n, (TList _), _)            = "\"" ++ n ++ "=\" & $ " ++ (toNimName n)
                generateSignatureBody' (n, (TDict _ _), _)          = "\"" ++ n ++ "=\" & $ " ++ (toNimName n)
                generateSignatureBody' (n, _,                    _) = "\"" ++ n ++ "=\" & $ " ++ (toNimName n)

            generateMainBody : Nat -> String -> String -> FsmIdStyle -> String -> List Parameter -> String
            generateMainBody idt fsmidcode n fsmIdStyle middleware ps
              = let isInSession = isInfixOf "session" middleware in
                    List.join "\n" $ List.filter nonblank [ (indent idt) ++ "let"
                                                          , (indent (idt + (indentDelta * 1))) ++ "callback = $rand(uint64)"
                                                          , (indent (idt + (indentDelta * 1))) ++ "fsmid = " ++ if fsmIdStyle == FsmIdStyleUrl then "id.parseBiggestUInt" else (if fsmIdStyle == FsmIdStyleSession then "session" else fsmidcode)
                                                          , (indent (idt + (indentDelta * 1))) ++ "args = {"
                                                          , (indent (idt + (indentDelta * 2))) ++ "\"TENANT\": $tenant,"
                                                          , (indent (idt + (indentDelta * 2))) ++ "\"GATEWAY\": ctx.gateway,"
                                                          , (indent (idt + (indentDelta * 2))) ++ "\"TASK\": \"PLAY-EVENT\","
                                                          , (indent (idt + (indentDelta * 2))) ++ "\"FSMID\": $fsmid,"
                                                          , (indent (idt + (indentDelta * 2))) ++ "\"EVENT\": " ++ (show (toUpper n)) ++ ","
                                                          , (indent (idt + (indentDelta * 2))) ++ "\"CALLBACK\": callback,"
                                                          , (indent (idt + (indentDelta * 2))) ++ "\"OCCURRED-AT\": $to_mytimestamp(now()),"
                                                          , if isInSession then (indent (idt + (indentDelta * 2))) ++ "\"TRIGGER\": $session," else ""
                                                          , generateEventArguments (idt + (indentDelta * 2)) ps
                                                          , (indent (idt + (indentDelta * 1))) ++ "}"
                                                          , (indent idt) ++ "discard await ctx.queue_redis.xadd(queue, @args)"
                                                          , (indent idt) ++ "result = await check_result(ctx.cache_redis, tenant, callback, 0)"
                                                          ]

            generateMiddleware : Nat -> String -> String -> String -> FsmIdStyle -> MetaValue -> List Parameter -> String
            generateMiddleware idt name fsmidcode n fsmIdStyle (MVString middleware) ps
              = let codes = if middleware /= ""
                               then [ (indent idt) ++ "let"
                                    , if fsmIdStyle == FsmIdStyleUrl then (indent (idt + (indentDelta * 1))) ++ "id = matches[0]" else ""
                                    , generateGetEventArguments (idt + indentDelta) ps
                                    , generateSignatureBody (idt + indentDelta) ps
                                    , (indent idt) ++ "check_" ++ (toNimName middleware) ++ "(request, ctx, \"POST|/" ++  (Data.List.join "/" (if fsmIdStyle == FsmIdStyleUrl then [name, "$2", n] else [name, n])) ++ (if fsmIdStyle == FsmIdStyleUrl then "|$1\" % [signbody, id]):" else "|$1\" % signbody):")
                                    , generateMainBody (idt + indentDelta) fsmidcode n fsmIdStyle middleware ps
                                    ]
                               else [ (indent idt) ++ "let"
                                    , if fsmIdStyle == FsmIdStyleUrl then (indent (idt + (indentDelta * 1))) ++ "id = matches[0]" else ""
                                    , generateGetEventArguments (idt + indentDelta) ps
                                    , generateSignatureBody (idt + indentDelta) ps
                                    , generateMainBody idt fsmidcode n fsmIdStyle middleware ps
                                    ] in
                    List.join "\n" $ List.filter nonblank codes
            generateMiddleware idt name fsmidcode n fsmIdStyle _ ps
              = generateMainBody idt fsmidcode n fsmIdStyle "" ps

    generateFetchObject : String -> String -> String
    generateFetchObject pre name
      = List.join "\n" [ "proc get_" ++ (toNimName name) ++ "*(request: Request, ctx: GatewayContext): Future[Option[ResponseData]] {.async, gcsafe, locks:0.} ="
                       , (indent indentDelta) ++ "var matches: array[1, string]"
                       , (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpGet and match(request.path.get(\"\"),  re\"^\\/" ++ name ++ "\\/(.+)$\", matches):"
                       , (indent (indentDelta * 2)) ++ "let"
                       , (indent (indentDelta * 3)) ++ "id = matches[0]"
                       , (indent (indentDelta * 3)) ++ "signbody = \"\""
                       , (indent (indentDelta * 2)) ++ "check_signature_security(request, ctx, \"GET|/" ++ name ++ "/$2|$1\" % [signbody, id]):"
                       , (indent (indentDelta * 3)) ++ "let"
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

    generateFetchLists : String -> String -> List1 State -> String
    generateFetchLists pre name ss
      = List1.join "\n\n" $ map (generateFetchList pre name) ss
      where
        generateFetchList : String -> String -> State -> String
        generateFetchList pre name (MkState n _ _ ms)
          = let middleware = case lookup "gateway.middleware" ms of
                                  Just (MVString mw) => mw
                                  _ => "signature-security-session"
                nimname = toNimName name in
                List.join "\n" $ List.filter nonblank [ "proc get_" ++ (toNimName n) ++ "_" ++ nimname ++ "_list*(request: Request, ctx: GatewayContext): Future[Option[ResponseData]] {.async, gcsafe, locks:0.} ="
                                                      , (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpGet and match(request.path.get(\"\"), re\"^\\/" ++ name ++ "\\/" ++ n ++ "\"):"
                                                      , (indent (indentDelta * 2)) ++ "let"
                                                      , (indent (indentDelta * 3)) ++ "params   = request.params"
                                                      , (indent (indentDelta * 3)) ++ "offset   = parseInt(params.getOrDefault(\"offset\", \"0\"))"
                                                      , (indent (indentDelta * 3)) ++ "limit    = parseInt(params.getOrDefault(\"limit\", \"10\"))"
                                                      , (indent (indentDelta * 3)) ++ "signbody = @[\"limit=\" & $limit, \"offset=\" & $offset].join(\"&\")"
                                                      , (indent (indentDelta * 2)) ++ "check_" ++ (toNimName middleware) ++ "(request, ctx, \"GET|/" ++ name ++ "/" ++ n ++ "|$1\" % signbody):"
                                                      , (indent (indentDelta * 3)) ++ "let"
                                                      , (indent (indentDelta * 4)) ++ "srckey = \"tenant:\" & $tenant & \"#" ++ name ++ "." ++ n ++ "\""
                                                      , (indent (indentDelta * 4)) ++ "total  = await ctx.cache_redis.zcard(srckey)"
                                                      , (indent (indentDelta * 4)) ++ "ids  = await ctx.cache_redis.zrevrange(srckey, offset, offset + limit - 1)"
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

    generateGetJsonCall : String -> String -> List Parameter -> String
    generateGetJsonCall pre name ps
      = let nimname = toNimName name
            (norms, refs) = splitParameters ps in
            List.join "\n" $ List.filter nonblank [ "proc get_" ++ nimname ++ "_json*(redis: AsyncRedis, tenant: uint64, key: string): Future[Option[JsonNode]] {.async.} ="
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
                                                  , (indent (indentDelta * 2)) ++ "idx += 1"
                                                  , (indent indentDelta) ++ "result = some(payload)"
                                                  ]
      where
        splitParameters : List Parameter -> (List Parameter, List (Parameter, String))
        splitParameters ps
          = splitParameters' ps [] []
          where
            splitParameters' : List Parameter -> List Parameter -> List (Parameter, String) -> (List Parameter, List (Parameter, String))
            splitParameters' []                   acc1 acc2 = (acc1, acc2)
            splitParameters' (p@(_, _, ms) :: xs) acc1 acc2 =  case lookup "reference" ms of
                                                                    Just (MVString r) => splitParameters' xs acc1 ((p, r) :: acc2)
                                                                    _ => splitParameters' xs (p :: acc1) acc2

        generateGetJsonHandler : Nat -> Name -> Tipe -> String
        generateGetJsonHandler idt n (TList _)   = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                                                                  , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, val.get.parseJson)"
                                                                  ]
        generateGetJsonHandler idt n (TDict _ _) = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                                                                  , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, val.get.parseJson)"
                                                                  ]
        generateGetJsonHandler idt n t           = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                                                                  , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, % " ++ (toNimFromString "val.get" t) ++ ")"
                                                                  ]

        generateGetReferenceJsonHandler : Nat -> Name -> Tipe -> String -> String
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
        defaultValue (TPrimType PTLong)   = "0'i64"
        defaultValue (TPrimType PTULong)  = "0'u64"
        defaultValue (TPrimType PTReal)   = "0.0"
        defaultValue (TPrimType PTString) = "\"\""
        defaultValue (TList _)            = "@[]"
        defaultValue _                    = "nil"

        generateDefaultGetJsonHandler : Nat -> Name -> Tipe -> String
        generateDefaultGetJsonHandler idt n t@(TDict _ _)
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, json.`%` " ++ (defaultValue t) ++ ")"
                           ]
        generateDefaultGetJsonHandler idt n t
          = List.join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                           , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, % " ++ (defaultValue t) ++ ")"
                           ]

    generateParticipants : String -> String -> List1 State -> List1 Transition -> List1 Participant -> String
    generateParticipants pre name ss ts ps
      = List1.join "\n\n" $ map (generateParticipant pre name ss ts) ps
      where
        generateParticipant : String -> String -> List1 State -> List1 Transition -> Participant -> String
        generateParticipant pre name ss ts p@(MkParticipant n _)
          = let eventRouters = nub $ flatten $ List1.toList $ map (generateEventCallsByParticipantAndTransition indentDelta name p) ts
                stateRouters = List1.toList $ map (generateStateCall indentDelta pre name) ss
                getObjRouter = (indent indentDelta) ++ "RouteProc[GatewayContext](" ++ (toNimName name) ++ ".get_" ++ (toNimName name) ++ ")"
                in
                List.join "\n" [ "let " ++ (toNimName n) ++ "_routers*: seq[RouteProc[GatewayContext]] = @["
                               , List.join ",\n" (getObjRouter :: (stateRouters ++ eventRouters))
                               , "]"
                               ]
          where
            generateEventCallsByParticipantAndTransition : Nat -> String -> Participant -> Transition -> List String
            generateEventCallsByParticipantAndTransition idt name p (MkTransition _ _ ts)
              = filter nonblank $ map (generateEventCallByParticipantAndTrigger idt name p) ts
              where
                generateEventCallByParticipantAndTrigger : Nat -> String -> Participant -> Trigger -> String
                generateEventCallByParticipantAndTrigger idt name p (MkTrigger ps e _ _)
                  = if elemBy (==) p ps
                       then (indent idt) ++ "RouteProc[GatewayContext](" ++ (toNimName name) ++ "." ++ (toNimName (Event.name e)) ++ ")"
                       else ""

            generateStateCall : Nat -> String -> String -> State -> String
            generateStateCall idt pre name (MkState n _ _ _)
              = (indent idt) ++ "RouteProc[GatewayContext](" ++ (toNimName name) ++ ".get_" ++ (toNimName n) ++ "_" ++ (toNimName name) ++ "_list)"


loadFsm : String -> Either String Fsm
loadFsm src
  = do (sexp, _) <- mapError parseErrorToString $ parseSExp src
       (fsm, _) <- mapError parseErrorToString $ analyse sexp
       fsm' <- mapError checkersErrorToString $ check fsm defaultCheckingRules
       pure fsm'

doWork : String -> IO ()
doWork src
  = do Right fsm <- loadFsmFromFile src
       | Left err => putStrLn $ show err
       putStrLn $ toNim fsm

usage : IO ()
usage
  = putStrLn "Usage: pfsm-to-nim-gateway <src>"

main : IO ()
main
  = do
    args <- getArgs
    case args of
         x0 :: x1 :: [] => doWork x1
         _ => usage
