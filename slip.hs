--                                                        -*- coding: utf-8 -*-
-- Auteurs: Laurent Mercier (20150219) et Andrei Bituleanu (20275298)
-- Date: 18 octobre 2024
--
-- Ce programme implante un évaluateur du langage Slip qui est un dérivé du 
-- langage Lisp. On définit les fonctionalités suivantes: un analyseur lexical,
-- un analyseur syntaxique, un pretty printer et une implantation du langage. 

-------------------------------------------------------------------------------
-- Pragmas utilisées pour le compilateur GHC. 
{-# OPTIONS_GHC -Wall #-}
{-# OPTIONS_GHC -Wno-incomplete-patterns #-}
{-# OPTIONS_GHC -Wno-incomplete-uni-patterns #-}
{-# OPTIONS_GHC -Wno-overlapping-patterns #-}

-------------------------------------------------------------------------------
-- Importations de librairies et définitions de fonctions auxiliaires.
-- Bibliothèque d'analyse syntaxique.
import Data.Char -- Conversion de Chars de/vers Int et autres.

-- Pour stdout, hPutStr.
import Data.Text.Encoding (decodeASCII)
import System.IO
import Text.ParserCombinators.Parsec

-------------------------------------------------------------------------------
-- La représentation interne des expressions de notre language.          
data Sexp
  = Snil -- La liste vide.
  | Ssym String -- Un symbole.
  | Snum Int -- Un entier.
  | Snode Sexp [Sexp] -- Une liste non vide.
  -- Génère automatiquement un pretty-printer et une fonction de
  -- comparaison structurelle.
  deriving (Show, Eq)

-- Exemples:
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
-- Analyseur lexical.                                                     
pChar :: Char -> Parser ()
pChar c = do _ <- char c; return ()

-- Les commentaires commencent par un point-virgule et se terminent
-- à la fin de la ligne.
pComment :: Parser ()
pComment = do
  pChar ';'
  _ <- many (satisfy (\c -> not (c == '\n')))
  (pChar '\n' <|> eof)
  return ()

-- N'importe quelle combinaison d'espaces et de commentaires est considérée
-- comme du blanc.
pSpaces :: Parser ()
pSpaces = do
  _ <- many (do { _ <- space; return () } <|> pComment)
  return ()

-- Un nombre entier est composé de chiffres.
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

-- Les symboles sont constitués de caractères alphanumériques et de signes
-- de ponctuations.
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
-- Analyseur syntaxique.                                                 
-- La notation "'E" est équivalente à "(quote E)".
pQuote :: Parser Sexp
pQuote = do
  pChar '\''
  pSpaces
  e <- pSexp
  return (Snode (Ssym "quote") [e])

-- Une liste est de la forme:  ( {e} [. e] ).
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

-- Accepte n'importe quel caractère: utilisé en cas d'erreur.
pAny :: Parser (Maybe Char)
pAny = do { c <- anyChar; return (Just c) } <|> return Nothing

-- Une Sexp peut-être une liste, un symbol ou un entier.
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

-- On distingue l'analyse syntaxique d'une Sexp principale de celle d'une
-- sous-Sexp: si l'analyse d'une sous-Sexp échoue à EOF, c'est une erreur de
-- syntaxe alors que si l'analyse de la Sexp principale échoue cela peut être
-- tout à fait normal.
pSexp :: Parser Sexp
pSexp = pSexpTop <|> error "Unexpected end of stream"

-- Une séquence de Sexps.
pSexps :: Parser [Sexp]
pSexps = do
  pSpaces
  many
    ( do
        e <- pSexpTop
        pSpaces
        return e
    )

-- Déclare que notre analyseur syntaxique peut-être utilisé pour la fonction
-- générique "read".
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

-- On peut utiliser notre pretty-printer pour la fonction générique "show"
-- (utilisée par la boucle interactive de GHCi).  Mais avant de faire cela,
-- il faut enlever le "deriving Show" dans la déclaration de Sexp.
{-
instance Show Sexp where
    showsPrec p = showSexp'
-}

-- Pour lire et imprimer des Sexp plus facilement dans la boucle interactive
-- de Hugs/GHCi:
readSexp :: String -> Sexp
readSexp = read

showSexp :: Sexp -> String
showSexp e = showSexp' e ""

-------------------------------------------------------------------------------
-- Représentation intermédiaire Lexp.                         
type Var = String

data Lexp
  = Lnum Int                 -- Constante entière.
  | Lbool Bool               -- Constante Booléenne.
  | Lvar Var                 -- Référence à une variable.
  | Ltest Lexp Lexp Lexp     -- Expression conditionnelle (if).
  | Lfob [Var] Lexp          -- Construction de fobjet (fonction).
  | Lsend Lexp [Lexp]        -- Appel de fobjet (fonction).
  | Llet Var Lexp Lexp       -- Déclaration non-récursive (let).
    -- Déclaration de fonctions mutuellement récursives.
  | Lfix [(Var, Lexp)] Lexp
  deriving (Show, Eq)

s2l :: Sexp -> Lexp

-- Cas pour transformer Snum en Lnum.
s2l (Snum n) = Lnum n

-- Cas pour transformer des chaînes "true" en Lbool True et "false" en 
-- Lbool False, sinon un string quelconque en Lvar.
s2l (Ssym s) = case s of
  "true"  -> Lbool True
  "false" -> Lbool False
  _       -> Lvar s

-- Cas pour construire une expression conditionnelle.
s2l (Snode (Ssym "if") [condition, thenCase, elseCase]) = 
  Ltest (s2l condition) (s2l thenCase) (s2l elseCase)

-- Cas pour créer une déclaration non-récursive.
s2l (Snode (Ssym "let") [Ssym var, val, expression]) = 
  Llet var (s2l val) (s2l expression)

-- Cas pour créer un fobjet (fonction). Prend en compte le cas où une fonction
-- est définie dans le corps de la fonction initiale.
s2l (Snode (Ssym "fob") [Snode (Ssym arg) args, body]) = 
  case body of
    (Snode (Ssym "fob") [Snode (Ssym arg') args', body']) ->
      Lfob (map (\(Ssym s) -> s) (Ssym arg : args) ++ 
            map (\(Ssym s) -> s) (Ssym arg' : args')) (s2l body')
    _ -> Lfob (map (\(Ssym s) -> s) (Ssym arg : args)) (s2l body)

-- Cas pour les déclarations récursives. On prend la liste des déclarations
-- de variables, de fonctions sucrées et de fonctions non sucrées et on les
-- convertit en paire (nom, déclaration) avec la fonction convertOnList qui 
-- agit récursivement sur la liste.
s2l (Snode (Ssym "fix") [Snode premier resteAttach, body]) =
  let 
      convertAttach (Snode (Ssym var) [expr]) = 
        (var, s2l expr)
      
      convertAttach (Snode (Snode (Ssym funcName) funcArgs) [funcDef]) = 
        (funcName, Lfob (map (\(Ssym s) -> s) funcArgs) (s2l funcDef))
      
      convertAttach (Snode (Ssym funcName) [fob]) = 
        (funcName, s2l fob)
      
      convertAttach _ = error "Attachement invalide"
      
      -- Conversion des éléments de la liste.
      convertOnList (element1 : reste) =
        if reste == []
          then [convertAttach element1]
          else convertAttach element1 : convertOnList reste
      
      attachList = convertOnList (premier : resteAttach)
   in 
      Lfix attachList (s2l body)

-- Cas pour traiter les appels de fonctions. Les appels peuvent contenir un 
-- fobjet, ou récursivement contenir un autre appel de fonction.
s2l (Snode sendNode vals) = case sendNode of
  (Snode (Ssym "fob") [Snil, Snum n]) -> s2l (Snum n)
  (Snode (Ssym "fob") _) -> 
    Lsend (s2l sendNode) (map s2l vals)
    
  (Snode sendNode' vals') -> 
    s2l (Snode sendNode' (vals' ++ vals))
    
  _ -> 
    Lsend (s2l sendNode) (map s2l vals)

-------------------------------------------------------------------------------
-- Représentation du contexte d'exécution.                                

data Value
  = Vnum Int                -- Valeur entière.
  | Vbool Bool              -- Valeur booléenne.
  | Vbuiltin ([Value] -> Value) -- Valeur de fonction prédéfinie.
  | Vfob VEnv [Var] Lexp    -- Valeur d'un fobjet.
  
instance Show Value where
  showsPrec p (Vnum n) = showsPrec p n
  showsPrec p (Vbool b) = showsPrec p b
  showsPrec _ (Vbuiltin _) = showString "<primitive>"
  showsPrec _ (Vfob _ _ _) = showString "<fobjet>"

type VEnv = [(Var, Value)]

env0 :: VEnv
env0 =
  let 
      -- Fonction pour créer des opérations binaires.
      binop f op =
        Vbuiltin
          ( \vs -> case vs of
              [Vnum n1, Vnum n2] -> f (n1 `op` n2)
              [_, _] -> error "Pas un nombre"
              _ -> error "Nombre d'arguments incorrect"
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
-- Évaluateur                                                            

-- Fonction d'évaluation des Lexp.
eval :: VEnv -> Lexp -> Value

-- Cas pour évaluer une constante entière.
eval _ (Lnum n) = Vnum n

-- Cas pour évaluer une constante booléenne.
eval _ (Lbool True) = Vbool True
eval _ (Lbool False) = Vbool False

-- Cas pour évaluer une expression conditionnelle.
eval env (Ltest e1 e2 e3) =
  let 
      condEval = eval env e1
   in 
      case condEval of
        Vbool True -> eval env e2
        Vbool False -> eval env e3

-- Cas pour évaluer une variable.
eval env (Lvar x) =
  case lookup x env of
    Just v -> v
    Nothing -> error ("Variable non-définie: " ++ x)

-- Cas pour évaluer un fobjet.
eval env (Lfob var expression) = Vfob env var expression

-- Cas pour évaluer un appel de fobjet. On doit tenir compte des variables 
-- évaluées dans l'environnement où l'on évalue la fonction. Lsend peut 
-- également appeller une fonction prédéfinie, dans quel cas on applique 
-- la fonction directement.
eval env (Lsend func vals) =
  case eval env func of
    Vfob env' args body ->
      let 
          valsEval = map (eval env) vals
          env'' = zip args valsEval ++ env'
       in 
          eval env'' body
    
    Vbuiltin f -> f (map (eval env) vals)
    
    _ -> error "Appel d'une fonction non-définie"

-- Cas pour évaluer une déclaration non-récursive.
eval env (Llet var val expression) =
  let 
      env' = zip [var] [eval env val] ++ env
   in 
      eval env' expression

-- Cas pour évaluer une déclaration récursive. On veut évaluer les déclarations
-- de façon récursive afin que les déclarations récursives au sein de fix 
-- fonctionnent.
eval env (Lfix contenu expr) =
  let
      -- Création de l'environnement pour les fonctions récursives.
      envRec = 
        map (\(name, value) -> (name, eval (envRec ++ env) value)) contenu
      newEnv = envRec ++ env
  in
      eval newEnv expr

-------------------------------------------------------------------------------
-- Toplevel.                                                              

evalSexp :: Sexp -> Value
evalSexp = eval env0 . s2l

-- Lit un fichier contenant plusieurs Sexps, les évalues l'une après
-- l'autre, et renvoie la liste des valeurs obtenues.
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
