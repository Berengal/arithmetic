{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}
{-# LANGUAGE PatternSynonyms #-}

module Math.Arithmetic where

import Control.Applicative

import Data.Char
import Data.List
import Data.Ord

data Expr where
  Lit :: Integer -> Expr
  Var :: Char -> Expr
  Plus :: Expr -> Expr -> Expr
  Mult :: Expr -> Expr -> Expr
  Pow :: Expr -> Expr -> Expr
  deriving (Show, Eq, Ord)

normal :: Expr -> Expr
normal (Lit n) = Lit n
normal (Var v) = Var v
normal (Plus a b) =
  case (normal a, normal b) of
    -- Literal reduction
    (Lit 0, b') -> b'
    (a', Lit 0) -> a'
    (Lit a', Lit b') -> Lit (a' + b')

    -- Listify tree
    (Plus a' b', c') -> Plus a' (Plus b' c')

    -- Sort variables
    -- TODO put this into some VarSum type and do the work there
    (Vars a', Vars b')
      | b' < a' -> Plus (Vars b') (Vars a')
    (Vars a', Mult (Lit b') (Vars c'))
      | c' < a' -> Plus (Mult (Lit b') (Vars c')) (Vars a')
    (Vars a', Plus (Vars b') c')
      | b' < a' -> Plus (Vars b') (Plus (Vars a') c')
    (Vars a', Plus (Mult (Lit b') (Vars c')) d')
      | c' < a' -> Plus (Mult (Lit b') (Vars c')) (Plus (Vars a') d')
    (Mult (Lit n') (Vars a'), Vars b')
      | b' < a' -> Plus (Vars b') (Mult (Lit n') (Vars a'))
    (Mult (Lit n') (Vars a'), Mult (Lit b') (Vars c'))
      | c' < a' -> Plus (Mult (Lit b') (Vars c')) (Mult (Lit n') (Vars a'))
    (Mult (Lit n') (Vars a'), Plus (Vars b') c')
      | b' < a' -> Plus (Vars b') (Plus (Mult (Lit n') (Vars a')) c')
    (Mult (Lit n') (Vars a'), Plus (Mult (Lit b') (Vars c')) d')
      | c' < a' -> Plus (Mult (Lit b') (Vars c')) (Plus (Mult (Lit n') (Vars a')) d')

    -- Contraction
    (a', b')
      | a' == b' -> Mult (Lit 2) a'
    (a', Plus b' c')
      | a' == b' -> Plus (Mult (Lit 2) a') c'
    (a', Plus (Mult (Lit b') c') d')
      | a' == c' -> Plus (Mult (Lit (b' + 1)) a') d'
    (Mult (Lit a') b', Mult (Lit c') d')
      | b' == d' -> Mult (Lit (a' + c')) b'
    -- Variable contraction must be done separately because Vars a == Vars b
    -- doesn't mean a == b
    (Vars a', Vars b')
      | a' == b' -> Mult (Lit 2) (Vars a')
    (Vars a', Mult (Lit b') (Vars c'))
      | a' == c' -> Mult (Lit (b' + 1)) (Vars a')
    (Vars a', Plus (Vars b') c')
      | a' == b' -> Plus (Mult (Lit 2) (Vars a')) c'
    (Vars a', Plus (Mult (Lit b') (Vars c')) d')
      | a' == c' -> Plus (Mult (Lit (b' + 1)) (Vars a')) d'
    (Mult (Lit a') (Vars b'), Vars c')
      | b' == c' -> Mult (Lit (a' + 1)) (Vars b')
    (Mult (Lit a') (Vars b'), Mult (Lit c') (Vars d'))
      | b' == d' -> Mult (Lit (a' + c')) (Vars b')
    (Mult (Lit a') (Vars b'), Plus (Vars c') d')
      | b' == c' -> Plus (Mult (Lit 2) (Vars b')) d'
    (Mult (Lit a') (Vars b'), Plus (Mult (Lit c') (Vars d')) e')
      | b' == d' -> Plus (Mult (Lit (a' + c')) (Vars b')) e'

    -- Default
    (a', b') -> Plus a' b'
normal (Mult a b) =
  case (normal a, normal b) of
    -- Literal reduction
    (Lit 0, b') -> Lit 0
    (a', Lit 0) -> Lit 0
    (Lit 1, b') -> b'
    (a', Lit 1) -> a'
    (Lit a', Lit b') -> Lit (a' * b')

    -- Listify tree
    (Mult a' b', c') -> Mult a' (Mult b' c')
    
    -- Move literals to the front
    (a', Lit b') -> Mult (Lit b') a'
    (Lit a', Mult (Lit b') c') -> Mult (Lit (a' * b')) c'
    (a', Mult (Lit b') c') -> Mult (Lit b') (Mult a' c')

    -- Power contraction
    (a', Pow b' c')
      | a' == b' -> Pow a' (Plus (Lit 1) c')
    (Pow a' b', c')
      | a' == c' -> Pow a' (Plus (Lit 1) b')
    (Pow a' e1', Pow b' e2')
      | a' == b' -> Pow a' (Plus e1' e2')

    -- Addition distribution
    (Plus a' b', c') -> Plus (Mult a' c') (Mult b' c')
    (a', Plus b' c') -> Plus (Mult a' b') (Mult a' c')

    -- Power introduction
    (Var a', Mult (Var b') c')
      | a' == b' -> Mult (Pow (Var a') (Lit 2)) c'
    (Var a', Mult (Pow (Var b') e') c')
      | a' == b' -> Mult (Pow (Var a') (Plus (Lit 1) e')) e'
    (Pow (Var a') e', Var b')
      | a' == b' -> Pow (Var a') (Plus (Lit 1) e')
    (Pow (Var a') e', Mult (Var b') c')
      | a' == b' -> Mult (Pow (Var a') (Plus (Lit 1) e')) c'
    (Pow (Var a') e', Pow (Var b') f')
      | a' == b' -> Pow (Var a') (Plus e' f')
    (Pow (Var a') e', Mult (Pow (Var b') f') c')
      | a' == b' -> Mult (Pow (Var a') (Plus e' f')) c'
    (a', b')
      | a' == b' -> Pow a' (Lit 2)
    -- Default
    (a', b') -> Mult a' b'
normal (Pow a b) =
  case (normal a, normal b) of
    -- Literal reduction
    (Lit a', Lit b') -> Lit (a' ^ b')
    (a', Lit 0) -> Lit 1
    (a', Lit 1) -> a'

    -- Powers of powers
    (Pow a' e', b') -> Pow a' (Mult e' b')

    -- Powers of compound expressions
    (Mult a' b', Lit e') -> Mult (Pow a' (Lit e')) (Pow b' (Lit e'))
    (Plus a' b', Lit e') -> Mult (Plus a' b') (Pow (Plus a' b') (Lit (e' - 1)))
    
    -- Default
    (a', b') -> Pow a' b'

stable :: Eq a => (a -> a) -> a -> a
stable f =
  last .
  foldr (\e r -> e:if null r || e == head r then [] else r) [] .
  iterate f

newtype VarProd = VarProd [(Char, Expr)]
  deriving (Show, Eq)

instance Ord VarProd where
  compare (VarProd a) (VarProd b) = compare (length a) (length b) <> compare a b

matchVars :: Expr -> Maybe [(Char, Expr)]
matchVars (Var a) = Just [(a, Lit 1)]
matchVars (Pow (Var a) e) = Just [(a, e)]
matchVars (Mult (Var a) (matchVars -> Just  r)) = Just $ (a, Lit 1):r
matchVars (Mult (Pow (Var a) e) (matchVars -> Just r)) = Just $ (a, e):r
matchVars _ = Nothing

buildVars :: [(Char, Expr)] -> Expr
buildVars = \case
  [v] -> build v
  (v:vs) -> Mult (build v) (buildVars vs)
  where
    build (v, Lit 1) = Var v
    build (v, Lit 0) = Lit 1
    build (v, e) = Pow (Var v) e

pattern Vars a <- (fmap (VarProd . sort) . matchVars -> Just a) where
  Vars (VarProd a) = buildVars a



newtype Parse a = Parse (String -> Maybe (String, a))

runParser :: Parse a -> String -> Maybe (String, a)
runParser (Parse p) = p

instance Functor Parse where
  fmap f (Parse g) = Parse $ fmap (fmap f) . g

instance Applicative Parse where
  pure x = Parse \s -> Just (s, x)
  Parse p <*> Parse q = Parse \s ->
    case p s of
      Nothing -> Nothing
      Just (ss, f) -> fmap f <$> q ss

instance Alternative Parse where
  empty = Parse $ const Nothing
  Parse p <|> Parse q = Parse \s ->
    case p s of
      Just v -> Just v
      Nothing -> q s

parse p s = case runParser p s of
  Nothing -> Nothing
  Just (_, r) -> Just r

isChar :: (Char -> Bool) -> Parse Char
isChar p = Parse \case
  (s:ss) | p s -> Just (ss, s)
  otherwise -> Nothing

char :: Char -> Parse Char
char c = isChar (==c)

alpha = isChar isAlpha
digit = isChar isDigit
space = isChar isSpace

anyChar :: Parse Char
anyChar = isChar (const True)

oneOf :: [Parse a] -> Parse a
oneOf [] = empty
oneOf [p] = p
oneOf [p,q] = p <|> q
oneOf list = let len = length list
                 (ps, qs) = splitAt (div len 2) list
             in oneOf ps <|> oneOf qs

times :: Int -> Parse a -> Parse [a]
times 0 _ = pure []
times n p = (:) <$> p <*> times (n-1) p

sepBy :: Parse a -> Parse b -> Parse [a]
sepBy p q = (:) <$> p <*> many (some q *> p)

expr :: Parse Expr
expr = many space *> (plusExpr <|> bracket expr) <* many space
  where
    ident c = many space *> char c <* many space
    bracket p = char '(' *> many space *> p <* many space <* char ')'
    lit = Lit . read <$> some digit
    var = Var <$> alpha
    atomicExpr = lit <|> var <|> bracket expr
    plusExpr = foldr1 Plus <$> (multExpr `sepBy` (ident '+'))
    multExpr = foldr1 Mult <$> some (powExpr <|> atomicExpr)
    powExpr = Pow <$> atomicExpr <*> (ident '^' *> atomicExpr)
    
type PPrint = String -> String

pChar c = (c:)
pString s = (s++)
pBracket s = pChar '(' . s . pChar ')'
pSepBy :: Char -> [PPrint] -> PPrint
pSepBy _ [] = id
pSepBy _ [s] = s
pSepBy c (s:ss) = s . pChar c . pSepBy c ss

pprintExpr :: Expr -> PPrint
pprintExpr (Lit n) = pString (show n)
pprintExpr (Var v) = pChar v
pprintExpr (Plus a b) = pSepBy ' ' [pprintExpr a, pChar '+', pprintExpr b]
pprintExpr (Mult a b) = bracketMult a . bracketMult b
  where bracketMult (Lit a) = pprintExpr (Lit a)
        bracketMult (Var a) = pprintExpr (Var a)
        bracketMult (Plus a b) = pBracket (pprintExpr (Plus a b))
        bracketMult (Mult a b) = pprintExpr a . pprintExpr b
        bracketMult (Pow (Var v) b) = pprintExpr (Pow (Var v) b)
        bracketMult (Pow a b) = pBracket (pprintExpr (Pow a b))
pprintExpr (Pow a b) = bracketCompound a . pChar '^' . bracketCompound b
  where
    bracketCompound (Lit n) = pprintExpr (Lit n)
    bracketCompound (Var v) = pprintExpr (Var v)
    bracketCompound e = pBracket (pprintExpr e)
    


pprint :: PPrint -> String
pprint = ($"")

prettyExpr :: Expr -> String
prettyExpr = pprint . pprintExpr

priters :: Int -> Expr -> IO ()
priters n = mapM_ print . take n . map prettyExpr . iterate normal 
