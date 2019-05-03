{-# LANGUAGE BlockArguments #-}
{-# LANGUAGE LambdaCase #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE ViewPatterns #-}

module Math.Arithmetic where

import Control.Applicative

import Data.Char

data Expr where
  Lit :: Integer -> Expr
  Var :: Char -> Expr
  Plus :: Expr -> Expr -> Expr
  Mult :: Expr -> Expr -> Expr
  Pow :: Expr -> Expr -> Expr
  deriving (Show, Eq)



eval :: Expr -> Integer
eval (Lit n) = n
eval (Var c) = undefined
eval (Plus a b) = eval a + eval b
eval (Mult a b) = eval a * eval b

simplify :: Expr -> Expr
simplify (Lit n) = Lit n
simplify (Var c) = Var c
simplify (Plus a b) =
  case (simplify a, simplify b) of
    (Lit 0, b') -> b'
    (a', Lit 0) -> a'
    (Lit a', Lit b') -> Lit (a'+b')
    (Var a', Var b') | a' == b' -> Mult (Lit 2) (Var a')
    (Mult (Lit x) (Var a'), Var b') | a' == b' -> Mult (Lit (x+1)) (Var a')
    (Var a', Mult (Lit y) (Var b')) | a' == b' -> Mult (Lit (y+1)) (Var b')
    (Mult (Lit x) (Var a'), Mult (Lit y) (Var b')) | a' == b' -> Mult (Lit (x+y)) (Var a')
    (a', b') -> Plus a' b'
simplify (Mult a b) =
  case (simplify a, simplify b) of
    (Lit 0, b') -> Lit 0
    (a', Lit 0) -> Lit 0
    (Lit 1, b') -> b'
    (a', Lit 1) -> a'
    (Lit a', Lit b') -> Lit (a'*b')
    (Var a', Var b')
      | a' == b' -> Mult (Lit 2) (Var a')
    (Var a', Lit b')
      -> Mult (Lit b') (Var a')
    (Mult (Lit x') (Var a'), Var b')
      -> Mult (Lit x') (Mult (Var a') (Var b'))
    (Var a', Mult (Lit y') (Var b'))
      -> Mult (Lit y') (Mult (Var a') (Var b'))
    (Mult (Lit x') (Var a'), Mult (Lit y') (Var b'))
      -> Mult (Lit (x'*y')) (Mult (Var a') (Var b'))
    (a', Plus b' c') -> Plus (simplify (Mult a' b')) (simplify (Mult a' c'))
    (a', b') -> Mult a' b'
simplify (Pow a b) =
  case (simplify a, simplify b) of
    (Lit 1, b') -> Lit 1
    (a', Lit 0) -> Lit 1
    (a', Lit 1) -> a'
    (Pow a' x', b') -> Pow a' (simplify $ Mult x' b')
    (a', b') -> Pow a' b'

matchVar :: Expr -> Maybe (Expr, [(Char, Expr)])
matchVar (Var v) = Just (Lit 1, [(v, Lit 1)])
matchVar (Pow (Var v) p) = Just (Lit 1, [(v, p)])
matchVar (Mult (Lit x) (matchVar -> (Lit 1, vars))) 
  = Just (Lit x, vars)
matchVar (Mult (Var v) (matchVar -> (Lit 1, vars))) 
  = Just (Lit 1, (v, Lit 1):vars)
matchVar (Mult (Pow (Var v) (Lit x)) (matchVar -> (Lit 1, vars)))
  = Just (Lit 1, (v, Lit x): vars)

newtype Parse a = Parse (String -> Maybe (String, a))

runParser :: Parse a -> String -> Maybe (String, a)
runParser (Parse p) = p

instance Functor Parse where
  fmap f (Parse g) = Parse $ fmap (fmap f) . g

instance Applicative Parse where
  pure x = Parse $ \s -> Just (s, x)
  Parse p <*> Parse q = Parse \s ->
    case p s of
      Nothing -> Nothing
      Just (ss, f) -> case q ss of
        Nothing -> Nothing
        Just (sss, a) -> Just (sss, f a)

instance Alternative Parse where
  empty = Parse $ const Nothing
  Parse p <|> Parse q = Parse $ \s ->
    case p s of
      Just v -> Just v
      Nothing -> q s

isChar :: (Char -> Bool) -> Parse Char
isChar p = Parse \case
  (s:ss) | p s -> Just (ss, s)
  otherwise -> Nothing

parse p s = case runParser p s of
  Nothing -> Nothing
  Just (_, r) -> Just r

char :: Char -> Parse Char
char c = isChar (==c)

alpha = isChar isAlpha
digit = isChar isDigit
space = isChar isSpace

anyChar :: Parse Char
anyChar = isChar (const True)

times :: Int -> Parse a -> Parse [a]
times 0 _ = pure []
times n p = (:) <$> p <*> times (n-1) p

sepBy :: Parse a -> Parse b -> Parse [a]
sepBy p q = (:) <$> p <*> many (some q *> p)

expr :: Parse Expr
expr = many space *> (lit
                      <|> var
                      <|> bracket
                      (plus
--                       <|>  minus
                       <|>  mult))
  where
    ident c = char c <* some space
    lit = Lit . read <$> some digit
    var = Var <$> alpha
    plus = Plus <$> (ident '+' *> expr) <*> expr
--    minus = Minus <$> (ident '-' *> expr) <*> expr
    mult = Mult <$> (ident '*' *> expr) <*> expr
    bracket p = char '(' *> many space *> p <* many space <* char ')'
