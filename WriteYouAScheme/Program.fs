module WriteYouAScheme

open System
open System.IO

module List =
    let split_at list n =
        let rec split_at' list' n' left right =
            match list' with
            | []      -> (List.rev left, List.rev right)
            | x :: xs -> if n' <= n then split_at' xs (n' + 1) (x :: left) right else split_at' xs (n' + 1) left (x :: right)
        split_at' list 0 [] []

    let drop list n =
        if n <= 0 then
            list
        else
            let (_, right) = split_at list (n - 1)
            right

    let rec last = function
        | hd :: [] -> hd
        | hd :: tl -> last tl
        | _ -> failwith "Empty list."

    let rec safeZip l1 l2 =
        match l1, l2 with
        | x1 :: xs1, x2 :: xs2 ->
            (x1, x2) :: (safeZip xs1 xs2)
        | [], _
        | _, [] -> []

module Expr =
    type PrimitiveFunc = LispVal list -> LispVal
    and IOFunc = LispVal list -> LispVal

    and Func = {
        Params: string list
        Vararg: string option
        Body: LispVal list
        Closure: Env 
    }

    and Env = Map<string, LispVal ref> ref

    and  LispVal =
        | Atom of string
        | List of LispVal list
        | DottedList of LispVal list * LispVal
        | Number of int
        | String of string
        | Bool of bool
        | PrimitiveFunc of PrimitiveFunc
        | Func of Func
        | IOFunc of IOFunc
        | Port of Stream
    with
        override __.ToString () =
            match __ with
            | String contents -> "\"" + contents + "\""
            | Atom name -> name
            | Number contents -> string contents
            | Bool true -> "#t"
            | Bool false -> "#f"
            | List contents -> 
                let contents = String.concat " " (List.map string contents)
                "(" + contents + ")"
            | (DottedList (head, tail)) -> 
                let headContents = String.concat " " (List.map string head)
                let tailContents = string tail
                "(" + headContents + " . " + tailContents + ")"
            | PrimitiveFunc _ -> "<primitive>"
            | Func { Params = args; Vararg = vararg; Body = body; Closure = env } ->
                let contents = String.concat " " (List.map string args)
                let middle = 
                    match vararg with
                    | Some arg -> " . " + arg
                    | _ -> ""
                "(lambda (" + contents + middle + ") ...)"
            | IOFunc _ -> "<IO primitive>"
            | Port _ -> "<IO port>"

module Error =
    open Expr

    type LispError =
        | NumArgs of int * LispVal list
        | TypeMismatch of string * LispVal
        | Parser of string
        | BadSpecialForm of string * LispVal
        | NotFunction of string * string
        | UnboundVar of string * string
        | Default of string
    with
        override __.ToString () =
            match __ with
            | UnboundVar (message, varname) -> message + ": " + varname
            | BadSpecialForm (message, form) -> message + ": " + (string form)
            | NotFunction (message, func) -> message + ": " + (string func)
            | NumArgs (expected, found) -> 
                let values = String.concat ", " (List.map string found)
                "Expected " + (string expected) + " args; found values " + values
            | TypeMismatch (expected, found) -> "Invalid type: expected " + expected + " found " + (string found)
            | Parser parseErr -> "Parser error at " + parseErr

    
exception LispError of Error.LispError
exception EnvError of string

module Parser =
    open Error

    open FParsec.CharParsers
    open FParsec.Primitives

    type ParserState = unit
    type Parser<'t> = Parser<'t, ParserState>

    let symbol: Parser<char> = 
        anyOf "!#$%&|*+-/:<=>?@^_~"

    let spaces: Parser<_> = spaces1

    let parseExpr, parseExprImpl = createParserForwardedToRef ()

    let parseString: Parser<Expr.LispVal> =
        let quote = pstring "\""
        between quote quote (manySatisfy (fun x -> x <> '"'))
        |>> Expr.String

    let parseAtom: Parser<Expr.LispVal> =
        let first = letter <|> symbol 
        let rest = many (letter <|> digit <|> symbol)
        pipe2 first rest (fun first rest ->
            let atom = String.Concat(Array.ofList (first :: rest))
            match atom with
            | "#t" -> Expr.Bool true
            | "#f" -> Expr.Bool false
            | _    -> Expr.Atom atom
        )

    let parseNumber: Parser<Expr.LispVal> = 
        pint32 |>> Expr.Number

    let rec parseList: Parser<Expr.LispVal> =
        sepBy parseExpr spaces |>> (fun list ->
            Expr.List list
        )

    and parseDottedList: Parser<Expr.LispVal> =
        let head = sepEndBy parseExpr spaces
        let tail = pstring "." >>. spaces >>. parseExpr
        pipe2 head tail (fun head tail ->
            Expr.DottedList (head, tail)
        )
    
    and parseQuoted: Parser<Expr.LispVal> =
        pstring "'" >>. parseExpr |>> (fun x -> 
            Expr.List [Expr.Atom "quote"; x]
        )       

    let list =
        pipe3 (pchar '(') (attempt parseList <|> parseDottedList) (pchar ')') (fun _ expr _ ->
            expr
        )

    do parseExprImpl :=
        choice [
            parseAtom
            parseString
            parseNumber
            parseQuoted
            list
        ]
    
    let inline readOrThrow (parser: Parser<'a,_>) input : 'a = 
        match run parser input with
        | ParserResult.Success (result, state, pos) -> result
        | ParserResult.Failure (se, e, state) -> raise (LispError (LispError.Parser se))
    let inline readExpr input = readOrThrow parseExpr input
    let inline readExprList input : Expr.LispVal list =
        let parser = (sepEndBy parseExpr spaces) 
        readOrThrow parser input

module Env =
    let createEnv () = ref Map.empty<string, Expr.LispVal ref>

    let isBound env var =
        !env
        |> Map.containsKey var

    let getVar env var =
        !env
        |> Map.tryFind var
        |> (function
            | Some value -> !value
            | _ -> raise (EnvError (sprintf "Getting an unbound variable %s" var))
        )

    let setVar (env: Expr.Env) var value =
        !env
        |> Map.tryFind var
        |> (function
            | Some prev -> prev := value
            | _ -> raise (EnvError (sprintf "Setting an unbound variable %s" var))
        )
        value

    let defineVar env var value =
        let alreadyDefined =
            !env
            |> Map.containsKey var
        if alreadyDefined then
            setVar env var value
        else
        env := 
            !env |> Map.add var (ref value)
        value
        
    let bindVars env bindings =
        let env = !env
        let env = ref env
        env :=
            bindings
            |> List.fold (fun env (var, value) ->
                env
                |> Map.add var (ref value)
            ) !env
        env

module Eval =
    open Expr

    let rec unpackNum = function
        | Number n -> n
        | String s -> 
            match Int32.TryParse s with
            | (true, n) -> n
            | _ -> raise (LispError (Error.LispError.TypeMismatch ("number", String s)))
        | List [n] -> unpackNum n
        | notNum -> raise (LispError (Error.LispError.TypeMismatch ("number", notNum)))

    let unpackStr = function
        | String s -> s
        | Number n -> string n
        | Bool b -> string b
        | notString -> raise (LispError (Error.LispError.TypeMismatch ("string", notString)))

    let unpackBool = function
        | Bool b -> b
        | notBool -> raise (LispError (Error.LispError.TypeMismatch ("boolean", notBool)))

    let numericBinop op args =
        match args with
        | [] -> raise (LispError (Error.NumArgs (2, [])))
        | [x] -> raise (LispError (Error.NumArgs (2, args)))
        | _ ->
            Number <| List.reduce op (List.map unpackNum args)

    let boolBinop unpacker op args =
        match args with
        | [left; right] ->
            let left = unpacker left
            let right = unpacker right
            Bool <| op left right
        | _ ->
            raise (LispError (Error.NumArgs (2, args)))

    let numBoolBinop = boolBinop unpackNum
    let strBoolBinop = boolBinop unpackStr
    let boolBoolBinop = boolBinop unpackBool

    let car = function
        | [List (x :: xs)] -> x
        | [DottedList ((x :: xs), _)] -> x
        | [badArg] -> raise (LispError (Error.LispError.TypeMismatch ("pair", badArg)))
        | badArgList -> raise (LispError (Error.LispError.NumArgs (1, badArgList)))

    let cdr = function
        | [List (x :: xs)] -> List xs
        | [DottedList ([_], x)] -> x
        | [DottedList ((_ :: xs), x)] -> DottedList (xs, x)
        | [badArg] -> raise (LispError (Error.LispError.TypeMismatch ("pair", badArg)))
        | badArgList -> raise (LispError (Error.LispError.NumArgs (1, badArgList)))

    let cons = function
        | [x1; List []] -> List [x1]
        | [x; List xs] -> List <| x :: xs
        | [x; DottedList (xs, xlast)] -> DottedList (x :: xs, xlast)
        | [x1; x2] -> DottedList ([x1], x2)
        | badArgList -> raise (LispError (Error.LispError.NumArgs (2, badArgList)))

    let rec eqv = function
        | [(Bool arg1); (Bool arg2)] -> Bool (arg1 = arg2)
        | [(Number arg1); (Number arg2)] -> Bool (arg1 = arg2)
        | [(String arg1); (String arg2)] -> Bool (arg1 = arg2)
        | [(Atom arg1); (Atom arg2)] -> Bool (arg1 = arg2)
        | [(DottedList (xs, x)); (DottedList (ys, y))] -> eqv [List (List.append xs [x]); List (List.append ys [y])]
        | [(List arg1); (List arg2)] ->
            try
                let eqvPair (x1, x2) = 
                    let (Bool v) = eqv [x1; x2] 
                    v
                Bool ((List.length arg1 = List.length arg2) && List.forall eqvPair (List.safeZip arg1 arg2))
            with
            | LispError e -> Bool false
        | [_; _] -> Bool false
        | badArgList -> raise (LispError (Error.LispError.NumArgs (2, badArgList)))

    let inline unpackEquals arg1 arg2 unpacker =
        try
            let unpacked1 = unpacker arg1
            let unpacked2 = unpacker arg2
            unpacked1 = unpacked2
        with
        | _ -> false

    let inline equal args =
        match args with
        | [arg1; arg2] ->
            let num = unpackEquals arg1 arg2 unpackNum
            let str = unpackEquals arg1 arg2 unpackStr
            let bool = unpackEquals arg1 arg2 unpackBool
            let (Bool eqvEquals) = eqv [arg1; arg2]
            Bool (num || str || bool || eqvEquals)

    let makePort mode access = function
        | [String filename] -> Expr.Port <| (File.Open(filename, mode, access) :> Stream)

    let closePort = function
        | [Expr.Port port] -> 
            port.Close ()
            Expr.Bool true
        | _ -> Expr.Bool false

    let rec readProc = function
        | [] -> readProc [Port (Console.OpenStandardInput ())]
        | [Port port] -> 
            use sr = new StreamReader(port)
            sr.ReadLine ()
            |> Parser.readExpr

    let rec writeProc = function
        | [obj] -> writeProc [Port (Console.OpenStandardOutput ())]
        | [obj; Port port] ->
            use sw = new StreamWriter(port)
            sw.WriteLine(obj)
            Expr.Bool true

    let readFile filename = 
        use fs = File.OpenRead(filename)
        use sr = new StreamReader(fs)
        sr.ReadToEnd()

    let readContents = function
        | [String filename] -> 
            Expr.String <| readFile filename

    let load filename = 
        Parser.readExprList <| readFile filename

    let readAll = function
        | [String filename] -> Expr.List (load filename)

    let rec applyProc exprs =
        match exprs with
        | [func; List args] -> apply func args
        | func :: args -> apply func args

    and ioPrimitives =
        Map.empty
        |> Map.add "apply" applyProc
        |> Map.add "open-input-file" (makePort FileMode.Open FileAccess.Read)
        |> Map.add "open-output-file" (makePort FileMode.OpenOrCreate FileAccess.ReadWrite)
        |> Map.add "close-input-port" closePort
        |> Map.add "close-output-port" closePort
        |> Map.add "read" readProc
        |> Map.add "write" writeProc
        |> Map.add "read-contents" readContents
        |> Map.add "read-all" readAll
        |> Map.toList

    and primitives =
        Map.empty
        |> Map.add "+" (numericBinop (+))
        |> Map.add "-" (numericBinop (-))
        |> Map.add "*" (numericBinop (*))
        |> Map.add "/" (numericBinop (/))
        |> Map.add "mod" (numericBinop (%))
        |> Map.add "=" (numBoolBinop (=))
        |> Map.add "<" (numBoolBinop (<))
        |> Map.add ">" (numBoolBinop (>))
        |> Map.add "/=" (numBoolBinop (<>))
        |> Map.add ">=" (numBoolBinop (>=))
        |> Map.add "<=" (numBoolBinop (<=))
        |> Map.add "&&" (boolBoolBinop (&&))
        |> Map.add "||" (boolBoolBinop (||))
        |> Map.add "string=?" (strBoolBinop (=))
        |> Map.add "string<?" (strBoolBinop (<))
        |> Map.add "string>?" (strBoolBinop (>))
        |> Map.add "string<=?" (strBoolBinop (<=))
        |> Map.add "string>=?" (strBoolBinop (>=))
        |> Map.add "car" car
        |> Map.add "cdr" cdr
        |> Map.add "cons" cons
        |> Map.add "eq?" eqv
        |> Map.add "eqv?" eqv
        |> Map.add "equal?" equal
        |> Map.toList

    and primitiveBindings =
        let makeFunc ctor (var, func) = (var, ctor func)
        List.map (makeFunc PrimitiveFunc) primitives
        |> List.append (List.map (makeFunc IOFunc) ioPrimitives)
        |> Env.bindVars (Env.createEnv ()) 

    and makeFunc varargs env parms body = 
        { 
            Params = (List.map string parms) 
            Vararg = varargs
            Body = body
            Closure = env
        }
        |> Func
    and makeNormalFunc = makeFunc None
    and makeVarArgs arg = makeFunc (Some (string arg))

    and apply func args = 
        match func with
        | PrimitiveFunc func -> func args
        | (Func { Params = parms; Vararg = vararg; Body = body; Closure = closure}) ->
            if List.length parms <> List.length args && vararg = None then
                raise (LispError (Error.LispError.NumArgs (List.length parms, args)))
            else
                let remainingArgs = List.drop args (List.length parms)
                let env = Env.bindVars closure (List.safeZip parms args)
                let env = 
                    match vararg with
                    | None -> env
                    | Some argName ->
                        Env.bindVars env [(argName, List remainingArgs)]
                List.map (eval env) body
                |> List.last
        | IOFunc func -> func args

    and eval (env: Env) lispVal =
        match lispVal with
        | String _
        | Number _
        | Bool _ -> lispVal
        | Atom id ->
            Env.getVar env id
        | List [Atom "quote"; lispVal] -> lispVal
        | List [Atom "if"; pred; conseq; alt] ->
            match eval env pred with
            | Bool false -> eval env alt
            | _ -> eval env conseq
        | List [Atom "set!"; Atom var; form] ->
            Env.setVar env var (eval env form)
        | List [Atom "define"; Atom var; form] ->
            Env.defineVar env var (eval env form)
        | List (Atom "define" :: List ((Atom var) :: parms) :: body) ->
            Env.defineVar env var <| makeNormalFunc env parms body
        | List (Atom "define" :: DottedList ((Atom var :: parms), varargs) :: body) ->
            Env.defineVar env var <| makeVarArgs varargs env parms body
        | List (Atom "lambda" :: List parms :: body) ->
            makeNormalFunc env parms body
        | List (Atom "lambda" :: DottedList (parms, varargs) :: body) ->
            makeVarArgs varargs env parms body
        | List (Atom "lambda" :: ((Atom _) as varargs) :: body) ->
            makeVarArgs varargs env [] body
        | List [Atom "load"; String filename] ->
            List.last (List.map (eval env) (load filename))
        | List (func :: args) -> 
            let func = eval env func
            let args = List.map (eval env) args
            apply func args
        | badForm -> raise (LispError (Error.LispError.BadSpecialForm ("unrecognized special form", badForm)))

module REPL =
    let flushStr str = printf "%s" str

    let readPrompt prompt = 
        flushStr prompt
        System.Console.ReadLine ()

    let evalString env expr =
        try
            let lispVal = Parser.readExpr expr
            let result = Eval.eval env lispVal
            string result
        with 
        | e -> sprintf "Error: %A" e

    let evalAndPrint env expr =
        printfn "%s" (evalString env expr)

    let rec until_ pred prompt action =
        let result = prompt ()
        if pred result then
            ()
        else
            action result
            until_ pred prompt action

    let runOne (args: string list) =
        let env = Env.bindVars Eval.primitiveBindings [("args", Expr.List (List.map Expr.String (List.drop args 1)))]
        let output = string <| Eval.eval env (Expr.List [Expr.Atom "load"; Expr.String (List.head args)])
        printfn "%s" output

    let runRepl () =
        let env = Eval.primitiveBindings
        until_ ((=) "quit") (fun () -> readPrompt "Lisp>>> ") (evalAndPrint env)

[<EntryPoint>]
let main argv = 
    if Array.length argv = 0 then
        REPL.runRepl ()
    else
        REPL.runOne (List.ofArray argv)

    0 // return an integer exit code
