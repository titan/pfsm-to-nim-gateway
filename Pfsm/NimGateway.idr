module Pfsm.NimGateway

import Data.Maybe
import Data.List
import Data.SortedMap
import Data.Strings
import System
import System.File

import Pfsm
import Pfsm.Analyser
import Pfsm.Checker
import Pfsm.Data
import Pfsm.Parser

indentDelta : Nat
indentDelta = 2

nonblank : String -> Bool
nonblank s = length s > Z

lookup : MetaKey -> List Meta -> Maybe MetaValue
lookup k ms
  = lookup' k ms Nothing
  where
    lookup' : MetaKey -> List Meta -> Maybe MetaValue -> Maybe MetaValue
    lookup' k []                      acc = acc
    lookup' k (m@(MkMeta k' v) :: ms) acc = if k == k'
                                               then Just v
                                               else lookup' k ms acc

nimBuiltinTypes : List String
nimBuiltinTypes = [ "int" , "int8" , "int16" , "int32" , "int64" , "uint" , "uint8" , "uint16" , "uint32" , "uint64" , "float" , "floa t32" , "float64" , "true" , "false" , "char" , "string" , "cstring" ]

nimKeywords : List String
nimKeywords = [ "addr" , "and" , "as" , "asm" , "bind" , "block" , "break" , "case" , "cast" , "concept" , "const" , "continue" , "converter" , "defer" , "discard" , "distinct" , "div" , "do" , "elif" , "else" , "end" , "enum" , "except" , "export" , "finally" , "for" , "from" , "func" , "if" , "import" , "in" , "include" , "interface" , "is" , "isnot" , "iterator" , "let" , "macro" , "method" , "mixin" , "mod" , "nil" , "not" , "notin" , "object" , "of" , "or" , "out" , "proc" , "ptr" , "raise" , "ref" , "return" , "shl" , "shr" , "static" , "template" , "try" , "tuple" , "type" , "using" , "var" , "when" , "while" , "xor" , "yield" ]

primToNimType : PrimType -> String
primToNimType t
  = case t of
         PTBool   => "bool"
         PTByte   => "uint8"
         PTChar   => "char"
         PTShort  => "int16"
         PTUShort => "uint16"
         PTInt    => "int"
         PTUInt   => "uint"
         PTLong   => "int64"
         PTULong  => "uint64"
         PTReal   => "float64"
         PTString => "string"

toNimName : Name -> String
toNimName n
  = let n' = normalize n in
    if elemBy (==) n' nimKeywords
       then "my_" ++ n'
       else n'
  where
    mappings : List (String, String)
    mappings =  [ (" ", "_")
                , ("-", "_")
                , ("+", "plus")
                ]
    normalize : Name -> String
    normalize n = foldl (\acc, x => replaceAll (fst x) (snd x) acc) n mappings

toNimType : Tipe -> String
toNimType TUnit          = "void"
toNimType (TPrimType t)  = primToNimType t
toNimType (TList t)      = "seq[" ++ (toNimType t) ++ "]"
toNimType (TDict k v)    = "table[" ++ (primToNimType k) ++ "," ++ (toNimType v) ++ "]"
toNimType (TRecord n ts) = toNimName n
toNimType t@(TArrow a b) = case liftArrowParams t [] of
                                []      => toNimFuncType []           TUnit
                                x :: xs => toNimFuncType (reverse xs) x
                        where
                          liftArrowParams : Tipe -> List Tipe -> List Tipe
                          liftArrowParams (TArrow a b@(TArrow _ _)) acc = liftArrowParams b (a :: acc)
                          liftArrowParams (TArrow a b)              acc = b :: (a :: acc)
                          liftArrowParams _                         acc = acc

                          toNimFuncType : List Tipe -> Tipe -> String
                          toNimFuncType as r
                              = let args = join ", " (map (\(i, x) => "a" ++ (show i) ++ ": " ++ toNimType(x)) (enumerate as))
                                    ret  = toNimType r in
                                    "proc (" ++ args ++ "): " ++ ret

toNimModelAttribute : String -> String
toNimModelAttribute "@" = "model"
toNimModelAttribute a
  = if isPrefixOf "@" a
       then "model." ++ toNimName (substr 1 (minus (length a) 1) a)
       else toNimName a

toNimExpression : String -> Expression -> String
toNimExpression "fsm.guard_delegate" (ApplicationExpression n es) = "fsm.guard_delegate" ++ "." ++ (toNimName n) ++ "(" ++ (join ", " (map (toNimExpression "fsm.guard_delegate") ((IdentifyExpression "model") :: es))) ++ ")"
toNimExpression caller (ApplicationExpression n es) = caller ++ "." ++ (toNimName n) ++ "(" ++ (join ", " (map (toNimExpression caller) es)) ++ ")"
toNimExpression _      (BooleanExpression True)     = "true"
toNimExpression _      (BooleanExpression False)    = "false"
toNimExpression _      (IdentifyExpression i)       = toNimModelAttribute i
toNimExpression _      (IntegerLiteralExpression i) = show i
toNimExpression _      (RealLiteralExpression r)    = show r
toNimExpression _      (StringLiteralExpression s)  = show s

toNimCompareOperation : CompareOperation -> String
toNimCompareOperation NotEqualsToOperation         = "!="
toNimCompareOperation EqualsToOperation            = "=="
toNimCompareOperation LessThanOperation            = "<"
toNimCompareOperation LessThanOrEqualsToOperation  = "<="
toNimCompareOperation GreatThanOperation           = ">"
toNimCompareOperation GreatThanOrEqualsToOperation = ">="

toNimTestExpression : TestExpression -> String
toNimTestExpression (PrimitiveTestExpression e) = toNimExpression "fsm.guard_delegate" e
toNimTestExpression (BinaryTestExpression op e1 e2) = (toNimTestExpression e1) ++ " " ++ (show op) ++ " " ++ (toNimTestExpression e2)
toNimTestExpression (UnaryTestExpression op e) = (show op) ++ " " ++ (toNimTestExpression e)
toNimTestExpression (CompareExpression op e1 e2) = (toNimExpression "fsm.guard_delegate" e1) ++ " " ++ (toNimCompareOperation op) ++ " " ++ (toNimExpression "fsm.guard_delegate" e2)

toNim : Fsm -> String
toNim fsm
  = let name = fsm.name
        pre = camelize (toNimName name)
        idfields = (filter idFieldFilter fsm.model) in
        join "\n\n" [ generateImports
                    , "const queue = " ++ (show (name ++ "-input"))
                    , generateEventCalls pre name idfields fsm.events
                    , generateGetJsonCall pre name fsm.model
                    , generateFetchLists pre name fsm.states
                    , generateParticipants pre name fsm.states fsm.transitions fsm.participants
                    ]
  where
    idFieldFilter : Parameter -> Bool
    idFieldFilter (_, _, Nothing) = False
    idFieldFilter (_, _, Just ms) = case lookup "fsmid" ms of
                                         Just (MVString "true") => True
                                         _ => False

    generateImports : String
    generateImports
      = join "\n" [ "import asyncdispatch, httpbeauty, httpbeast, json, options, random, re, sequtils, strtabs, strutils, utility"
                  , "import redis except `%`"
                  ]

    generateEventCalls : String -> String -> List Parameter -> List Event -> String
    generateEventCalls pre name idfields es
      = let fsmidcode = "generate_fsmid($tenant & \"-" ++ name ++ "-\" & " ++ (join " & " (map (\(n, t, _) => "$" ++ (toNimName n)) idfields)) ++ ")" in
            join "\n\n" $ map (generateEvent pre name fsmidcode) es
      where
        generateEvent : String -> String -> String -> Event -> String
        generateEvent pre name fsmidcode (MkEvent n ps ms)
          = let ms' = fromMaybe [] ms
                withoutId = isJust $ lookup "gateway.without-id" ms'
                middleware = fromMaybe (MVString "") $ lookup "gateway.middleware" ms' in
                join "\n" $ filter nonblank [ "proc " ++ (toNimName n) ++ "*(request: Request, tenant: uint64, queue_redis: AsyncRedis, cache_redis: AsyncRedis): Future[Option[ResponseData]] {.async, gcsafe, locks:0.} ="
                                            , if not withoutId then (indent indentDelta) ++ "var matches: array[1, string]" else ""
                                            , if not withoutId then (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpPost and match(request.path.get(\"\"), re\"^\\/" ++ name ++ "\\/(.+)\\/" ++ n ++ "$\", matches):" else (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpPost and request.path.get(\"\") == \"/" ++ name ++ "\""
                                            , generateMiddleware (indentDelta * 2) fsmidcode n withoutId middleware ps
                                            , (indent indentDelta) ++ "else:"
                                            , (indent (indentDelta * 2)) ++ "result = none(ResponseData)"
                                            ]

          where
            typeWrapper : String -> Tipe -> String
            typeWrapper s (TPrimType PTBool)   = s ++ "getBool"
            typeWrapper s (TPrimType PTByte)   = "cast[uint8](" ++ s ++ ".getInt)"
            typeWrapper s (TPrimType PTShort)  = "cast[int16](" ++ s ++ ".getInt)"
            typeWrapper s (TPrimType PTUShort) = "cast[uint16](" ++ s ++ ".getInt)"
            typeWrapper s (TPrimType PTInt)    = s ++ ".getInt"
            typeWrapper s (TPrimType PTUInt)   = "cast[uint](" ++ s ++ ".getInt)"
            typeWrapper s (TPrimType PTLong)   = s ++ ".getBiggestInt"
            typeWrapper s (TPrimType PTULong)  = "cast[uint64](" ++ s ++ ".getBiggestInt)"
            typeWrapper s (TPrimType PTReal)   = s ++ ".getFloat"
            typeWrapper s (TPrimType PTChar)   = "if len(" ++ s ++ ".getStr) > 0: " ++ s ++ ".getStr()[0] else: '\\0'"
            typeWrapper s (TPrimType PTString) = s ++ ".getStr"
            typeWrapper s (TList t)            = s ++ ".getElems.mapIt(" ++ (typeWrapper "it" t) ++ ")"
            typeWrapper s (TDict PTString t)   = s ++ ".getFields.mapIt((it[0], " ++ (typeWrapper "it[1]" t) ++ "))"
            typeWrapper s _                    = s

            generateGetEventArgument : Nat -> Parameter -> String
            generateGetEventArgument idt (n, t, _)
              = let lhs = (indent idt) ++ (toNimName n)
                    rhs = typeWrapper ("data{" ++ (show n) ++ "}") t in
                    lhs ++ " = " ++ rhs

            generateGetEventArguments : Nat -> List Parameter -> String
            generateGetEventArguments idt [] = ""
            generateGetEventArguments idt ps = join "\n" [ (indent idt) ++ "data = parseJson(request.body.get(\"{}\"))"
                                                         , join "\n" $ map (generateGetEventArgument idt) ps
                                                         ]

            toNimArg : Name -> Tipe -> String
            toNimArg n (TPrimType PTString) = n
            toNimArg n (TPrimType _) = "$" ++ n
            toNimArg n (TList t) = "\"[\" & " ++ n ++ ".mapIt(" ++ (toNimArg "it" t) ++ ").join(\",\") & \"]\""
            toNimArg n (TDict k v) = "\"[\" & dictpair.mapIt(\"(\" & " ++ (toNimArg "it[0]" (TPrimType k)) ++ " & \",\" & " ++ (toNimArg "it[1]" v) ++ " & \")\") & \"]\""
            toNimArg n _ = n

            generateEventArgument : Nat -> Parameter -> String
            generateEventArgument idt (n, t, _)
              = (indent idt) ++ (show (toUpper n)) ++ ": " ++ toNimArg (toNimName n) t ++ ","

            generateEventArguments : Nat -> List Parameter -> String
            generateEventArguments idt ps
              = join "\n" $ map (generateEventArgument idt) ps

            generateSignatureBody : Nat -> List Parameter -> String
            generateSignatureBody idt ps
              = let items = map generateSignatureBody' ps in
                    if length items > Z
                       then (indent idt) ++ "signbody = @[" ++ (join ", " items) ++ "].join(\"&\")"
                       else (indent idt) ++ "signbody = \"\""
              where
                generateSignatureBody' : Parameter -> String
                generateSignatureBody' (n, (TPrimType PTString), _) = "\"" ++ n ++ "=\" & " ++ (toNimName n)
                generateSignatureBody' (n, _,                    _) = "\"" ++ n ++ "=\" & $" ++ (toNimName n)

            generateMainBody : Nat -> String -> String -> Bool -> List Parameter -> String
            generateMainBody idt fsmidcode n withoutId ps
              = join "\n" $ filter nonblank [ (indent idt) ++ "let"
                                            , (indent (idt + (indentDelta * 1))) ++ "callback = $rand(uint64)"
                                            , (indent (idt + (indentDelta * 1))) ++ "fsmid = " ++ if not withoutId then "fromHex[BiggestUInt](id)" else fsmidcode
                                            , (indent (idt + (indentDelta * 1))) ++ "args = {"
                                            , (indent (idt + (indentDelta * 2))) ++ "\"TENANT\": $tenant,"
                                            , (indent (idt + (indentDelta * 2))) ++ "\"TASK-TYPE\": \"PLAY-EVENT\","
                                            , (indent (idt + (indentDelta * 2))) ++ "\"FSMID\": $fsmid,"
                                            , (indent (idt + (indentDelta * 2))) ++ "\"EVENT\": " ++ (show (toUpper n)) ++ ","
                                            , (indent (idt + (indentDelta * 2))) ++ "\"CALLBACK\": callback,"
                                            , generateEventArguments (idt + (indentDelta * 2)) ps
                                            , (indent (idt + (indentDelta * 1))) ++ "}"
                                            , (indent idt) ++ "discard await queue_redis.xadd(queue, @args)"
                                            , (indent idt) ++ "result = await check_result(cache_redis, callback, 0)"
                                            ]

            generateMiddleware : Nat -> String -> String -> Bool -> MetaValue -> List Parameter -> String
            generateMiddleware idt fsmidcode n withoutId (MVString middleware) ps
              = let codes = if middleware /= ""
                               then [ (indent idt) ++ "let"
                                    , generateGetEventArguments (idt + indentDelta) ps
                                    , generateSignatureBody (idt + indentDelta) ps
                                    , (indent idt) ++ "check_" ++ (toNimName middleware) ++ ":"
                                    , generateMainBody (idt + indentDelta) fsmidcode n withoutId ps
                                    ]
                               else [ (indent idt) ++ "let"
                                    , generateGetEventArguments (idt + indentDelta) ps
                                    , generateSignatureBody (idt + indentDelta) ps
                                    , generateMainBody idt fsmidcode n withoutId ps
                                    ] in
                    join "\n" $ filter nonblank codes
            generateMiddleware idt fsmidcode n withoutId _ ps
              = generateMainBody idt fsmidcode n withoutId ps

    generateFetchLists : String -> String -> List State -> String
    generateFetchLists pre name ss
      = join "\n\n" $ map (generateFetchList pre name) ss
      where
        generateFetchList : String -> String -> State -> String
        generateFetchList pre name (MkState n _ _ _)
          = let nimname = toNimName name in
                join "\n" $ filter nonblank [ "proc get_" ++ (toNimName n) ++ "_" ++ nimname ++ "_list*(request: Request, tenant: uint64, queue_redis: AsyncRedis, cache_redis: AsyncRedis): Future[Option[ResponseData]] {.async, gcsafe, locks:0.} ="
                                            , (indent indentDelta) ++ "if request.httpMethod.get(HttpGet) == HttpGet and match(request.path.get(\"\"), re\"^\\/" ++ name ++ "\\/" ++ n ++ "\"):"
                                            , (indent (indentDelta * 2)) ++ "let"
                                            , (indent (indentDelta * 3)) ++ "params = request.params"
                                            , (indent (indentDelta * 3)) ++ "offset = parseInt(params.getOrDefault(\"offset\", \"0\"))"
                                            , (indent (indentDelta * 3)) ++ "limit  = parseInt(params.getOrDefault(\"limit\", \"10\"))"
                                            , (indent (indentDelta * 3)) ++ "srckey = \"tenant:\" & $tenant & \"#" ++ name ++ "." ++ n ++ "\""
                                            , (indent (indentDelta * 3)) ++ "total  = await cache_redis.zcard(srckey)"
                                            , (indent (indentDelta * 3)) ++ "ids  = await cache_redis.zrevrange(srckey, offset, offset + limit - 1)"
                                            , (indent (indentDelta * 2)) ++ "var items = newJArray()"
                                            , (indent (indentDelta * 2)) ++ "for id in ids:"
                                            , (indent (indentDelta * 3)) ++ "let"
                                            , (indent (indentDelta * 4)) ++ "key = " ++ "\"tenant:\" & $tenant & \"#" ++ name ++ ":\" & id"
                                            , (indent (indentDelta * 4)) ++ "itemopt = await get_" ++ nimname ++ "_json(cache_redis, key)"
                                            , (indent (indentDelta * 3)) ++ "if " ++ "itemopt.isSome:"
                                            , (indent (indentDelta * 4)) ++ "var item = itemopt.get"
                                            , (indent (indentDelta * 4)) ++ "item.add(\"fsmid\", %id)"
                                            , (indent (indentDelta * 4)) ++ "items.add(item)"
                                            , (indent (indentDelta * 2)) ++ "var pagination = newJObject()"
                                            , (indent (indentDelta * 2)) ++ "pagination.add(\"total\", % total)"
                                            , (indent (indentDelta * 2)) ++ "pagination.add(\"offset\", % offset)"
                                            , (indent (indentDelta * 2)) ++ "pagination.add(\"limit\", % limit)"
                                            , (indent (indentDelta * 2)) ++ "var ret = newJObject()"
                                            , (indent (indentDelta * 2)) ++ "ret.add(\"pagination\", pagination)"
                                            , (indent (indentDelta * 2)) ++ "ret.add(\"data\", items)"
                                            , (indent (indentDelta * 2)) ++ "resp(ret)"
                                            , (indent indentDelta) ++ "else:"
                                            , (indent (indentDelta * 2)) ++ "result = none(ResponseData)"
                                            ]

    generateGetJsonCall : String -> String -> List Parameter -> String
    generateGetJsonCall pre name ps
      = let nimname = toNimName name in
            join "\n" [ "proc get_" ++ nimname ++ "_json(redis: AsyncRedis, key: string): Future[Option[JsonNode]] {.async.} ="
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
                      , join "\n" $ map (\(n, t, _) => generateGetJsonHandler (indentDelta * 4) n t) ps
                      , (indent (indentDelta * 4)) ++ "else:"
                      , (indent (indentDelta * 5)) ++ "payload.add(fields[idx].toLowerAscii, % val.get)"
                      , (indent (indentDelta * 2)) ++ "else:"
                      , (indent (indentDelta * 3)) ++ "case fields[idx]:"
                      , join "\n" $ map (\(n, t, _) => generateDefaultGetJsonHandler (indentDelta * 4) n t) ps
                      , (indent (indentDelta * 4)) ++ "else:"
                      , (indent (indentDelta * 5)) ++ "payload.add(fields[idx].toLowerAscii, % \"\")"
                      ]
      where
        generateGetJsonHandler : Nat -> Name -> Tipe -> String
        generateGetJsonHandler idt n t
          = join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                      , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, % " ++ (typeWrapper "val.get" t) ++ ")"
                      ]
          where
            typeWrapper : String -> Tipe -> String
            typeWrapper s (TPrimType PTBool)   = s ++ ".parseBool"
            typeWrapper s (TPrimType PTByte)   = "cast[uint8](" ++ s ++ ".parseInt)"
            typeWrapper s (TPrimType PTShort)  = "cast[int16](" ++ s ++ ".parseInt)"
            typeWrapper s (TPrimType PTUShort) = "cast[uint16](" ++ s ++ ".parseUInt)"
            typeWrapper s (TPrimType PTInt)    = s ++ ".parseInt"
            typeWrapper s (TPrimType PTUInt)   = s ++ ".parseUInt"
            typeWrapper s (TPrimType PTLong)   = s ++ ".parseBiggestInt"
            typeWrapper s (TPrimType PTULong)  = s ++ ".parseBiggestUInt"
            typeWrapper s (TPrimType PTReal)   = s ++ ".parseFloat"
            typeWrapper s (TPrimType PTChar)   = "if len(" ++ s ++ ") > 0: " ++ s ++ "[0] else: '\\0'"
            typeWrapper s (TPrimType PTString) = s
            typeWrapper s (TList t)            = s ++ ".parseList.mapIt(" ++ (typeWrapper "it" t) ++ ")"
            typeWrapper s (TDict PTString t)   = s ++ ".parseDict.mapIt((it[0], " ++ (typeWrapper "it[1]" t) ++ "))"
            typeWrapper s _                    = s

        generateDefaultGetJsonHandler : Nat -> Name -> Tipe -> String
        generateDefaultGetJsonHandler idt n t
          = join "\n" [ (indent idt) ++ "of " ++ (show (toUpper n)) ++ ":"
                      , (indent (idt + indentDelta)) ++ "payload.add(fields[idx].toLowerAscii, % " ++ (defaultValue t) ++ ")"
                      ]
          where
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

    generateParticipants : String -> String -> List State -> List Transition -> List Participant -> String
    generateParticipants pre name ss ts ps
      = join "\n\n" $ map (generateParticipant pre name ss ts) ps
      where
        generateParticipant : String -> String -> List State -> List Transition -> Participant -> String
        generateParticipant pre name ss ts p@(MkParticipant n _)
          = let event_routers = nub $ flatten $ map (generateEventCallsByParticipantAndTransition indentDelta p) ts
                state_routers = map (generateStateCall indentDelta pre name) ss in
                join "\n" [ "const " ++ (toNimName n) ++ "_routers* = @["
                          , join ",\n" $ (state_routers ++ event_routers)
                          , "]"
                          ]
          where
            generateEventCallsByParticipantAndTransition : Nat -> Participant -> Transition -> List String
            generateEventCallsByParticipantAndTransition idt p (MkTransition _ _ ts)
              = filter nonblank $ map (generateEventCallByParticipantAndTrigger idt p) ts
              where
                generateEventCallByParticipantAndTrigger : Nat -> Participant -> Trigger -> String
                generateEventCallByParticipantAndTrigger idt p (MkTrigger ps e _ _)
                  = if elemBy (==) p ps
                       then (indent idt) ++ "RouteProc(" ++ (toNimName (Event.name e)) ++ ")"
                       else ""

            generateStateCall : Nat -> String -> String -> State -> String
            generateStateCall idt pre name (MkState n _ _ _)
              = (indent idt) ++ "RouteProc(get_" ++ (toNimName n) ++ "_" ++ (toNimName name) ++ "_list)"


loadFsm : String -> Either String Fsm
loadFsm src
  = case parseSExp src of
         Left (Error e _) => Left e
         Right (sexp, _) => case analyse sexp of
                                 Left (Error e _) => Left e
                                 Right (fsm, _) => case check fsm defaultCheckingRules of
                                                        Just errs => Left $ foldl (\a, x => a ++ "\n" ++ x) "" errs
                                                        Nothing => Right fsm

doWork : String -> IO ()
doWork src
  = do
    r <- readFile src
    case r of
         Left e => putStrLn $ show e
         Right c => case loadFsm c of
                         Left e => putStrLn $ e
                         Right fsm => putStrLn $ toNim fsm

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
