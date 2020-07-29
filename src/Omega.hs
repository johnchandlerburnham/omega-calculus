{-# LANGUAGE OverloadedStrings #-}
module Omega where

import           Data.Text (Text)
import qualified Data.Text as T
import           Prelude   hiding (print)

import           Data.Void
import           Control.Monad.Identity
import           Control.Monad.State.Strict

import           Data.Map (Map)
import qualified Data.Map as M

import           Text.Megaparsec                hiding (State)
import           Text.Megaparsec.Char
import qualified Text.Megaparsec.Char.Lexer     as L

import Debug.Trace

type Name = Text
type Kind = Text

data Loc = Loc Int Int deriving Eq
noLoc = Loc 0 0

data Term
  = Var Loc Name
  | Lam Loc Name Term
  | App Loc Term Term
  | Par Loc Kind Term Term
  | Let Loc Kind Name Name Term Term
  deriving Eq

print :: Term -> Text
print t = case t of
  Var _ n         -> n
  Lam _ n b       -> T.concat ["λ", n, ". ", print b]
  App _ f a       -> T.concat ["(", print f, " ", print a, ")"]
  Par _ k l r     -> T.concat ["[", k, "|", print l, ",", print r, "]"]
  Let _ k l r x b -> T.concat ["let [",k,"|", l,",",r, "] = ",print x, "; ",print b]

instance Show Term where
  show term = T.unpack $ print term

type Parser = ParsecT Void Text Identity

name :: Parser Text
name = takeWhile1P
  (Just "a name (alphanumeric,'_','.')") (flip elem $ nameChar)
  where
    nameChar = ['0'..'9'] ++ ['a'..'z'] ++ ['A'..'Z'] ++ "_"

spaceC :: Parser ()
spaceC = L.space space1 (L.skipLineComment "//") (L.skipBlockComment "#" "#")

symbol :: Text -> Parser Text
symbol = L.symbol spaceC

term :: Parser Term
term = do
  from <- getOffset
  t    <- choice $
    [ label "\n - an abstraction: \"ωx. b\"" $ do
        from <- getOffset
        string "λ"
        name <- name <* spaceC <* symbol "."
        body <- term
        upto <- getOffset
        let l = Loc from upto
        return $ Lam l name body
    , label "\n - an application: \"(f a)\"" $ do
        from <- getOffset
        symbol "("
        func <- term
        argm <- term
        symbol ")"
        upto <- getOffset
        let l = Loc from upto
        return $ App l func argm
    , label "\n - a pair: \"[A|x,y]\"" $ do
        from <- getOffset
        symbol "["
        kind <- name
        symbol "|"
        val0 <- term
        symbol ","
        val1 <- term
        symbol "]"
        upto <- getOffset
        let l = Loc from upto
        return $ Par l kind val0 val1
    , label "\n - a definition: \"let [A|a,b] = x; body\"" $ do
        symbol "let"
        symbol "["
        kind <- name
        symbol "|"
        nam0 <- name
        symbol ","
        nam1 <- name
        symbol "]"
        symbol "="
        expr <- term <* symbol ";"
        body <- term
        upto <- getOffset
        let l = Loc from upto
        return $ Let l kind nam0 nam1 expr body
    , label "\n - a variable: \"x\"" $ do
        from <- getOffset
        name <- name
        upto <- getOffset
        let l = Loc from upto
        return $ Var l name
    ]
  spaceC
  return t

data Env = Env { _rwts :: Int, _size :: Int, _env :: Map Name Term } deriving Show

fresh :: State Env Text
fresh = do
  s <- gets _size
  modify (\e -> e { _size = (_size e) + 1})
  return $ T.concat ["$", T.pack $ show s]

reduce :: Term -> State Env Term
reduce term = let nl = noLoc in
  case term of
    Lam _ name body    -> do
      ---- traceM ("Lam: " ++ show term)
      body <- reduce body
      return $ Lam nl name body
    App _ func argm -> do
      -- traceM ("App: " ++ show term)
      func <- reduce func
      case func of
        Lam _ name body -> do
          -- traceM "App-Lam"
          env <- gets _env
          modify (\e -> e { _rwts = (_rwts e) + 1,
                            _env = M.insert name argm (_env e)
                          })
          reduce body
        Par _ kind val0 val1 -> do
          -- traceM "App-Par"
          modify (\e -> e { _rwts = (_rwts e) + 1})
          x0 <- fresh
          x1 <- fresh
          let a0 = App nl val0 (Var nl x0)
          let a1 = App nl val1 (Var nl x1)
          reduce (Let nl kind x0 x1 argm (Par nl kind a0 a1))
        Let _ kind nam0 nam1 expr body -> do
          -- traceM "App-Let"
          modify (\e -> e { _rwts = (_rwts e) + 1})
          reduce (Let nl kind nam0 nam1 expr (App nl body argm))
        _ -> do
         argm <- reduce argm
         return $ App nl func argm
    Par _ kind val0 val1 -> do
      -- traceM ("Par: " ++ show term)
      val0 <- reduce val0
      val1 <- reduce val1
      return $ Par nl kind val0 val1
    Let _ kind nam0 nam1 expr body -> do
      -- traceM ("Let: " ++ show term)
      expr <- reduce expr
      case expr of
        Lam _ expr_name expr_body -> do
          -- traceM "Let-Lam"
          modify (\e -> e { _rwts = (_rwts e) + 1})
          n0 <- fresh
          n1 <- fresh
          x0 <- fresh
          x1 <- fresh
          modify (\e -> e {_env =
            M.insert nam0 (Lam nl x0 (Var nl n0)) $
            M.insert nam1 (Lam nl x1 (Var nl n1)) $
            M.insert expr_name (Par nl kind (Var nl x0) (Var nl x1)) $ 
            (_env e) })
          reduce (Let nl kind n0 n1 expr_body body)
        Par _ expr_kind val0 val1 -> do
          -- traceM "Let-Par"
          modify (\e -> e { _rwts = (_rwts e) + 1})
          if kind == expr_kind then do
            -- traceM "Let-Par: True"
            modify (\e -> e {_env =
              M.insert nam0 val0 $
              M.insert nam1 val1 $
              (_env e) })
            reduce body
          else do
            -- traceM "Let-Par: False"
            x0 <- fresh
            x1 <- fresh
            y0 <- fresh
            y1 <- fresh
            modify (\e -> e {_env =
              M.insert nam0 (Par nl expr_kind (Var nl x0) (Var nl x1)) $
              M.insert nam1 (Par nl expr_kind (Var nl y0) (Var nl y1)) $
              (_env e) })
            let done = Let nl kind x0 y0 val0 (Let nl kind x1 y1 val1 body)
            ---- traceM $ "done: " ++ (show done)
            reduce done
        Let _ expr_kind expr_nam0 expr_nam1 expr_expr expr_body -> do
          -- traceM "Let-Let"
          modify (\e -> e { _rwts = (_rwts e) + 1})
          let done = Let nl kind nam0 nam1 expr_body body
          reduce (Let nl expr_kind expr_nam0 expr_nam1 expr_expr done)
        _ -> do
         body <- reduce body
         return $ Let nl kind nam0 nam1 expr body
    Var _ n -> do
      -- traceM ("Var: " ++ show term)
      env <- gets _env
      case env M.!? n of
        Just t -> do
          -- traceM ("Var got: " ++ T.unpack n ++ " = " ++ show t)
          modify (\e -> e {_env = M.delete n (_env e)})
          reduce t
        Nothing   -> do
          -- traceM ("Var not got: " ++ T.unpack n)
          return term

normalize :: Term -> (Term, Env)
normalize t = runState (loop t (-1)) (Env 0 1 M.empty)
  where
    loop :: Term -> Int ->  State Env Term
    loop t last_rwts = do
      env_rwts <- gets _rwts
      if env_rwts /= last_rwts then do
        t <- reduce t
        loop t env_rwts
      else return t



