--                                                        -*- coding: utf-8 -*-
-- Author: Laurent Mercier.
-- Date: October 18, 2024.
--
-- This program implementes an interpreter of the Slip language, which is based 
-- on the syntax of the Lisp programming language.
-- langage Lisp. The following functionalities have been implemented by Stefan 
-- Monnier: the lexical analyzer, the syntactic analyzer, and the pretty 
-- printer. I have implemented the language implementation (i.e. the s2l and
-- eval functions). 

-------------------------------------------------------------------------------
-- Pragmas used for the GHC compiler.
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

-------------------------------------------------------------------------------
-- Library imports and auxiliary function definitions.
-- Parsing library.
import Data.Char -- Conversion of Chars to/from Int and others.

-- For stdout, hPutStr.
import Data.Text.Encoding (decodeASCII)
import System.IO
import Text.ParserCombinators.Parsec

-------------------------------------------------------------------------------
-- The internal representation of expressions in our language.          
data Sexp
  = Snil -- The empty list.
  | Ssym String -- A symbol.
  | Snum Int -- An integer.
  | Snode Sexp [Sexp] -- A non-empty list.
  -- Automatically generates a pretty-printer and a structural comparison 
  -- function.
  deriving (Show, Eq)

-- Examples:
-- (+ 2 3) ==> Snode (Ssym "+")
--                   [Snum 2, Snum 3]
--
-- (/ (* (- 68 32) 5) 9)
--     ==>
-- Snode (Ssym "/")
--       [Snode (Ssym "*")
--              [Snode (Ssym "-")
--                     [Snum 68, Snum 32],
--               Snum 5],
--        Snum 9]

-------------------------------------------------------------------------------
-- Lexical analyzer.                                                     
pChar :: Char -> Parser ()
pChar c = do _ <- char c; return ()

-- Comments start with a semicolon and end at the end of the line.
pComment :: Parser ()
pComment = do
  pChar ';'
  _ <- many (satisfy (\c -> not (c == '\n')))
  (pChar '\n' <|> eof)
  return ()

-- Any combination of spaces and comments is considered whitespace.
pSpaces :: Parser ()
pSpaces = do
  _ <- many (do { _ <- space; return () } <|> pComment)
  return ()

-- An integer consists of digits.
integer :: Parser Int
integer =
  do
    c <- digit
    integer' (digitToInt c)
    <|> do
      _ <- satisfy (\c -> (c == '-'))
      n <- integer
      return (-n)
  where
    integer' :: Int -> Parser Int
    integer' n =
      do
        c <- digit
        integer' (10 * n + (digitToInt c))
        <|> return n

-- Symbols consist of alphanumeric characters and punctuation marks.
pSymchar :: Parser Char
pSymchar = alphaNum <|> satisfy (\c -> c `elem` "!@$%^&*_+-=:|/?<>")

pSymbol :: Parser Sexp
pSymbol = do
  s <- many1 (pSymchar)
  return
    ( case parse integer "" s of
        Right n -> Snum n
        _ -> Ssym s
    )

-------------------------------------------------------------------------------
-- Syntactic analyzer.                                                 
-- The notation "'E" is equivalent to "(quote E)".
pQuote :: Parser Sexp
pQuote = do
  pChar '\''
  pSpaces
  e <- pSexp
  return (Snode (Ssym "quote") [e])

-- A list has the form: ( {e} [. e] ).
pList :: Parser Sexp
pList = do
  pChar '('
  pSpaces
  ses <- pTail
  return
    ( case ses of
        [] -> Snil
        se : ses' -> Snode se ses'
    )

pTail :: Parser [Sexp]
pTail =
  do pChar ')'; return []
    -- <|> do { pChar '.'; pSpaces; e <- pSexp; pSpaces;
    --          pChar ')' <|> error ("Missing ')' after: " ++ show e);
    --          return e }
    <|> do e <- pSexp; pSpaces; es <- pTail; return (e : es)

-- Accepts any character: used in case of errors.
pAny :: Parser (Maybe Char)
pAny = do { c <- anyChar; return (Just c) } <|> return Nothing

-- A Sexp can be a list, a symbol, or an integer.
pSexpTop :: Parser Sexp
pSexpTop = do
  pSpaces
  pList
    <|> pQuote
    <|> pSymbol
    <|> do
      x <- pAny
      case x of
        Nothing -> pzero
        Just c -> error ("Unexpected char '" ++ [c] ++ "'")

-- We differentiate parsing a main Sexp from parsing a sub-Sexp: if parsing
-- a sub-Sexp fails at EOF, it's a syntax error, whereas if parsing the main
-- Sexp fails, it can be perfectly normal.
pSexp :: Parser Sexp
pSexp = pSexpTop <|> error "Unexpected end of stream"

-- A sequence of Sexps.
pSexps :: Parser [Sexp]
pSexps = do
  pSpaces
  many
    ( do
        e <- pSexpTop
        pSpaces
        return e
    )

-- Declares that our syntactic analyzer can be used for the generic "read" 
-- function.
instance Read Sexp where
  readsPrec _p s = case parse pSexp "" s of
    Left _ -> []
    Right e -> [(e, "")]

-------------------------------------------------------------------------------
-- Sexp Pretty Printer.                                                   
showSexp' :: Sexp -> ShowS
showSexp' Snil = showString "()"
showSexp' (Snum n) = showsPrec 0 n
showSexp' (Ssym s) = showString s
showSexp' (Snode h t) =
  let showTail [] = showChar ')'
      showTail (e : es) =
        showChar ' ' . showSexp' e . showTail es
   in showChar '(' . showSexp' h . showTail t

-- We can use our pretty-printer for the generic "show" function
-- (used by the GHCi interactive loop). But before doing this,
-- we need to remove the "deriving Show" in the Sexp declaration.
{-
instance Show Sexp where
    showsPrec p = showSexp'
-}

-- To read and print Sexps more easily in the Hugs/GHCi interactive loop:
readSexp :: String -> Sexp
readSexp = read

showSexp :: Sexp -> String
showSexp e = showSexp' e ""

-------------------------------------------------------------------------------
-- Intermediate representation Lexp.                         
type Var = String

data Lexp
  = Lnum Int                 -- Integer constant.
  | Lbool Bool               -- Boolean constant.
  | Lvar Var                 -- Variable reference.
  | Ltest Lexp Lexp Lexp     -- Conditional expression (if).
  | Lfob [Var] Lexp          -- Object function construction.
  | Lsend Lexp [Lexp]        -- Object function call.
  | Llet Var Lexp Lexp       -- Non-recursive declaration (let).
    -- Declaration of mutually recursive functions.
  | Lfix [(Var, Lexp)] Lexp
  deriving (Show, Eq)

s2l :: Sexp -> Lexp

-- Case to transform Snum into Lnum.
s2l (Snum n) = Lnum n

-- Case to transform the strings "true" into Lbool True and "false" into 
-- Lbool False, otherwise any other string into Lvar.
s2l (Ssym s) = case s of
  "true"  -> Lbool True
  "false" -> Lbool False
  _       -> Lvar s

-- Case to construct a conditional expression.
s2l (Snode (Ssym "if") [condition, thenCase, elseCase]) = 
  Ltest (s2l condition) (s2l thenCase) (s2l elseCase)

-- Case to create a non-recursive declaration.
s2l (Snode (Ssym "let") [Ssym var, val, expression]) = 
  Llet var (s2l val) (s2l expression)

-- Case to create a function object (fob). Handles the case where a function
-- is defined inside the body of the initial function.
s2l (Snode (Ssym "fob") [Snode (Ssym arg) args, body]) = 
  case body of
    (Snode (Ssym "fob") [Snode (Ssym arg') args', body']) ->
      Lfob (map (\(Ssym s) -> s) (Ssym arg : args) ++ 
            map (\(Ssym s) -> s) (Ssym arg' : args')) (s2l body')
    _ -> Lfob (map (\(Ssym s) -> s) (Ssym arg : args)) (s2l body)

-- Case for recursive declarations. We take the list of variable declarations,
-- sweet functions, and non-sweet functions and convert them into pairs 
-- (name, declaration) using the recursive function convertOnList.
s2l (Snode (Ssym "fix") [Snode premier resteAttach, body]) =
  let 
      convertAttach (Snode (Ssym var) [expr]) = 
        (var, s2l expr)
      
      convertAttach (Snode (Snode (Ssym funcName) funcArgs) [funcDef]) = 
        (funcName, Lfob (map (\(Ssym s) -> s) funcArgs) (s2l funcDef))
      
      convertAttach (Snode (Ssym funcName) [fob]) = 
        (funcName, s2l fob)
      
      convertAttach _ = error "Invalid attachment"
      
      -- Conversion of list elements.
      convertOnList (element1 : reste) =
        if reste == []
          then [convertAttach element1]
          else convertAttach element1 : convertOnList reste
      
      attachList = convertOnList (premier : resteAttach)
   in 
      Lfix attachList (s2l body)

-- Case to process function calls. Calls may contain a function object, or 
-- recursively contain another function call.
s2l (Snode sendNode vals) = case sendNode of
  (Snode (Ssym "fob") [Snil, Snum n]) -> s2l (Snum n) -- Constant function.
  (Snode (Ssym "fob") _) -> 
    Lsend (s2l sendNode) (map s2l vals) 
    
  (Snode sendNode' vals') -> 
    s2l (Snode sendNode' (vals' ++ vals)) -- Recursively defined function.
    
  _ -> 
    Lsend (s2l sendNode) (map s2l vals)

-------------------------------------------------------------------------------
-- Representation of the execution context.

data Value
  = Vnum Int                -- Integer value.
  | Vbool Bool              -- Boolean value.
  | Vbuiltin ([Value] -> Value) -- Built-in function value.
  | Vfob VEnv [Var] Lexp    -- Function object value.
  
instance Show Value where
  showsPrec p (Vnum n) = showsPrec p n
  showsPrec p (Vbool b) = showsPrec p b
  showsPrec _ (Vbuiltin _) = showString "<primitive>"
  showsPrec _ (Vfob _ _ _) = showString "<fobject>"

type VEnv = [(Var, Value)]

env0 :: VEnv
env0 =
  let 
      -- Function to create binary operations.
      binop f op =
        Vbuiltin
          ( \vs -> case vs of
              [Vnum n1, Vnum n2] -> f (n1 `op` n2)
              [_, _] -> error "Not a number"
              _ -> error "Incorrect number of arguments"
          )
   in 
      [ ("+", binop Vnum (+)),
        ("*", binop Vnum (*)),
        ("/", binop Vnum div),
        ("-", binop Vnum (-)),
        ("<", binop Vbool (<)),
        (">", binop Vbool (>)),
        ("≤", binop Vbool (<=)),
        ("≥", binop Vbool (>=)),
        ("=", binop Vbool (==)),
        ("true", Vbool True),
        ("false", Vbool False)
      ]

-------------------------------------------------------------------------------
-- Evaluator

-- Function to evaluate Lexp.
eval :: VEnv -> Lexp -> Value

-- Case to evaluate an integer constant.
eval _ (Lnum n) = Vnum n

-- Case to evaluate a boolean constant.
eval _ (Lbool True) = Vbool True
eval _ (Lbool False) = Vbool False

-- Case to evaluate a conditional expression.
eval env (Ltest e1 e2 e3) =
  let 
      condEval = eval env e1
   in 
      case condEval of
        Vbool True -> eval env e2
        Vbool False -> eval env e3

-- Case to evaluate a variable.
eval env (Lvar x) =
  case lookup x env of
    Just v -> v
    Nothing -> error ("Undefined variable: " ++ x)

-- Case to evaluate a function object.
eval env (Lfob var expression) = Vfob env var expression

-- Case to evaluate a function call. We must account for the variables 
-- evaluated in the environment where the function is being evaluated. 
-- Lsend can also call a built-in function, in which case the function is 
-- applied directly.
eval env (Lsend func vals) =
  case eval env func of
    Vfob env' args body ->
      let 
          valsEval = map (eval env) vals
          env'' = zip args valsEval ++ env'
       in 
          eval env'' body
    
    Vbuiltin f -> f (map (eval env) vals)
    
    _ -> error "Undefined function call"

-- Case to evaluate a non-recursive declaration.
eval env (Llet var val expression) =
  let 
      env' = zip [var] [eval env val] ++ env
   in 
      eval env' expression

-- Case to evaluate a recursive declaration. We want to evaluate the 
-- declarations recursively so that recursive declarations within `fix` work.
eval env (Lfix contenu expr) =
  let
      -- Creation of the environment for recursive functions.
      envRec = 
        map (\(name, value) -> (name, eval (envRec ++ env) value)) contenu
      newEnv = envRec ++ env
  in
      eval newEnv expr

-------------------------------------------------------------------------------
-- Toplevel.

evalSexp :: Sexp -> Value
evalSexp = eval env0 . s2l

-- Reads a file containing multiple Sexps, evaluates them one after another, 
-- and returns the list of obtained values.
run :: FilePath -> IO ()
run filename =
  do
    inputHandle <- openFile filename ReadMode
    hSetEncoding inputHandle utf8
    s <- hGetContents inputHandle
    (hPutStr stdout . show)
      ( let sexps s' = case parse pSexps filename s' of
              Left _ -> [Ssym "#<parse-error>"]
              Right es -> es
         in map evalSexp (sexps s)
      )
    hClose inputHandle

sexpOf :: String -> Sexp
sexpOf = read

lexpOf :: String -> Lexp
lexpOf = s2l . sexpOf

valOf :: String -> Value
valOf = evalSexp . sexpOf

-------------------------------------------------------------------------------
