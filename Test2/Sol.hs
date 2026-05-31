{-# LANGUAGE DerivingStrategies #-}
{-# LANGUAGE GeneralisedNewtypeDeriving #-}

module Test2.Sol where

import Text.Parsec
import Text.Parsec.Expr
import Data.Map (Map)
import Data.Map qualified as Map

import Control.Monad.Except
import Control.Monad.Reader
import Control.Concurrent.MVar

-- Leonardo López 25-91752
-- Carla Gómez 25-91750

data Tipo = TNum
          | TBool
          | TFun Tipo Tipo
          deriving (Eq)

instance Show Tipo where
    show TNum = "R"
    show TBool = "B"
    show (TFun t1 t2) = "(" ++show t1 ++ " -> " ++ show t2  ++ ")"

data Operador = Add | Sub | Mul | Div | Exp
    deriving (Eq)

instance Show Operador where
    show Add = "+"
    show Sub = "-"
    show Mul = "*"
    show Div = "/"
    show Exp = "^"

data Expr = Var String
          | Lambda String Tipo Expr
          | App Expr Expr
          | If Expr Expr Expr
          | Seq [Expr]
          | Let String Tipo Expr
          | Assign String Expr
          | Num Double
          | Boolean Bool
          | Print Expr
          | Operation Operador Expr Expr
          | Neg Expr
          deriving (Eq)

instance Show Expr where
    showsPrec _ (Var x) = showString x
    showsPrec p (Lambda x t e) = showParen (p > 0) $
        showString "/. " . showString x . showString " : " . showString (show t) .
        showString " => " . showsPrec 0 e
    showsPrec p (App e1 e2) = showParen (p > 10) $
        showsPrec 10 e1 . showChar ' ' . showsPrec 11 e2
    showsPrec p (If c e1 e2) = showParen (p > 0) $
        showString "if "   . showsPrec 0 c  .
        showString " then " . showsPrec 0 e1 .
        showString " else " . showsPrec 0 e2
    showsPrec p (Seq es) = showParen (p > 0) $
        foldr1 (\a b -> a . showString "; " . b) (map (showsPrec 1) es)
    showsPrec _ (Let x t e) =
        showString "let " . showString x . showString " : " . showString (show t) .
        showString " := " . showsPrec 0 e
    showsPrec _ (Assign x e) =
        showString x . showString " := " . showsPrec 0 e
    showsPrec p (Num n)     = showsPrec p n
    showsPrec _ (Boolean b) = showString $ if b then "true" else "false"
    showsPrec p (Print e)   = showParen (p > 10) $
        showString "print " . showsPrec 11 e
    showsPrec p (Operation op e1 e2) = showParen (p > prec) $
        showsPrec lp e1 . showString (" " ++ show op ++ " ") . showsPrec rp e2
      where
        (prec, lp, rp) = case op of
            Add -> (5, 5, 6)
            Sub -> (5, 5, 6)
            Mul -> (7, 7, 8)
            Div -> (7, 7, 8)
            Exp -> (8, 9, 8)
    showsPrec p (Neg e) = showParen (p > 6) $
        showChar '-' . showsPrec 7 e
    
typeCheck :: Map String Tipo -> Expr -> Either String Tipo
typeCheck env (Var x) = case Map.lookup x env of
        Just t -> Right t
        Nothing -> Left $ "Variable " ++ x ++ " not declared"
typeCheck env (Lambda x t e) = case typeCheck (Map.insert x t env) e of
        Right t' -> Right $ TFun t t'
        Left err -> Left err
typeCheck env (App e1 e2) = case (t1, t2) of
    (Left err, _) -> Left err
    (_, Left err) -> Left err
    (Right (TFun argType retType), Right t2') -> if argType == t2'
        then Right retType
        else Left $ "Type mismatch: expected " ++ show argType ++ ", found " ++ show t2'
    (Right t1', _) -> Left $ "Type error: expected a function, found " ++ show t1'
    where
        t1 = typeCheck env e1
        t2 = typeCheck env e2
typeCheck env (If cond block1 block2) = case typeCheck env cond of
    Right TBool -> checkBranches
    Right TNum  -> checkBranches
    Right t     -> Left $ "Type error: expected B or R, found " ++ show t
    Left err    -> Left err
  where
    checkBranches = case (typeCheck env block1, typeCheck env block2) of
        (Right t1, Right t2) -> if t1 == t2
            then Right t1
            else Left $ "Type mismatch in branches: " ++ show t1 ++ " and " ++ show t2
        (Left err, _) -> Left err
        (_, Left err) -> Left err
typeCheck env (Seq es) = laMalandra env es
    where 
        laMalandra env [x] = case typeCheck env x of
            Right t -> Right t
            Left err -> Left err
        laMalandra env (x:xs) = case x of
            Let var t e -> case typeCheck (Map.insert var t env) e of
                Right t' -> if t == t'
                    then laMalandra (Map.insert var t env) xs
                    else Left $ "Type mismatch in let: declared " ++ show t ++ ", found " ++ show t'
                Left err -> Left err
            e -> case typeCheck env e of
                Right _ -> laMalandra env xs
                Left err -> Left err
        laMalandra env [] = Right TBool -- Shouldn't be reachable anyway
typeCheck env (Let x t e) = case typeCheck (Map.insert x t env) e of
    Right t' -> if t == t'
        then Right t
        else Left $ "Type mismatch in let: declared " ++ show t ++ ", found " ++ show t'
    Left err -> Left err
typeCheck env (Assign x e) = case Map.lookup x env of
    Just t -> case typeCheck env e of
        Right t' -> if t == t'
            then Right t
            else Left $ "Type mismatch in assignment: variable " ++ x ++ " has type " ++ show t ++ " but assigned expression has type " ++ show t'
        Left err -> Left err
    Nothing -> Left $ "Variable " ++ x ++ " not declared"
typeCheck env (Num _) = Right TNum
typeCheck env (Boolean _) = Right TBool
typeCheck env (Print e) = typeCheck env e
typeCheck env (Neg e) = case typeCheck env e of
    Right TNum -> Right TNum
    Right t    -> Left $ "Type error in negation: expected R, found " ++ show t
    Left err   -> Left err
typeCheck env (Operation op e1 e2) = case (typeCheck env e1, typeCheck env e2) of
    (Right TNum, Right TNum) -> Right TNum
    (Right t1, Right t2) -> Left $ "Type error in operation: expected R and R, found " ++ show t1 ++ " and " ++ show t2
    (Left err, _) -> Left err
    (_, Left err) -> Left err

keywords :: [String]
keywords = ["if", "then", "else", "true", "false", "let", "print"]

pWhiteSpace :: Parsec String () ()
pWhiteSpace = skipMany $ space <|> newline <|> crlf <|> tab

pBoolean :: Parsec String () Expr
pBoolean = try (Boolean True <$ string "true") <|> try (Boolean False <$ string "false")

pNumber :: Parsec String () Expr
pNumber = f
    <$> many1 digit
    <*> optionMaybe (try (char '.' *> many1 digit))
    <*> optionMaybe (try
        ( (char 'e' <|> char 'E')
        *> pure (,)
        <*> optionMaybe (char '+' <|> char '-')
        <*> many1 digit
        ))
    where
    f :: [Char] -> Maybe [Char] -> Maybe (Maybe Char, [Char]) -> Expr
    f intPart mFrac mExp =
        let frac = maybe "" ('.' :) mFrac
            expStr = case mExp of
                Nothing -> ""
                Just (mSign', expPart) -> "e" <> maybe "" (:[]) mSign' <> expPart
        in Num $ read $ intPart <> frac <> expStr

pTipo' :: Parsec String () Tipo
pTipo' = between (char '(') (char ')') pTipo 
                <|> (TNum <$ string "R") 
                <|> (TBool <$ string "B")

pTipo :: Parsec String () Tipo
pTipo = f <$> pTipo' <* pWhiteSpace <*>
    (Just <$> (pWhiteSpace *> string "->" *> pWhiteSpace *> pTipo)
    <|> pure Nothing
    )
    where
        f :: Tipo -> Maybe Tipo -> Tipo
        f t1 Nothing = t1
        f t1 (Just t2) = TFun t1 t2

pVar :: Parsec String () Expr
pVar = try $ notFollowedBy pKeyword *>
    (merge <$> identifierStart <*> many identifierChar <*> identifierEnd)
    where
        pKeyword :: Parsec String () ()
        pKeyword = choice $ map keyword keywords
        keyword :: String -> Parsec String () ()
        keyword s = try $ string s *> notFollowedBy (alphaNum <|> char '_' <|> char '\'')
        identifierStart :: Parsec String () Char
        identifierStart = letter <|> char '_'
        identifierChar :: Parsec String () Char
        identifierChar = alphaNum <|> char '_'
        identifierEnd :: Parsec String () String
        identifierEnd = many (char '\'')
        merge :: Char -> String -> String -> Expr
        merge start middle end = Var $ start : middle ++ end

pLambda :: Parsec String () Expr
pLambda = string "/." *> pWhiteSpace *>
    (Lambda
    <$> (extractString <$> pVar )
    <*> (pWhiteSpace *> char ':' *> pWhiteSpace *> pTipo)
    <*> (pWhiteSpace *> string "=>" *> pWhiteSpace *> pExpr))
    where
        extractString :: Expr -> String
        extractString (Var s) = s
        extractString _ = error "Expected a variable"

pApp :: Parsec String () Expr
pApp = f <$> pExpr' <*> many1 (try (skipMany1 (space <|> tab <|> newline <|> crlf) *> pExpr'))
    where
        f :: Expr -> [Expr] -> Expr
        f = foldl App

pIf :: Parsec String () Expr
pIf = If
    <$> (string "if" *> pWhiteSpace *> pExpr)
    <*> (pWhiteSpace *> string "then" *> pWhiteSpace *> pExpr)
    <*> (pWhiteSpace *> string "else" *> pWhiteSpace *> pExpr)

pSeq :: Parsec String () Expr
pSeq = f <$> pExpr <* pWhiteSpace <*> many (char ';' *> pWhiteSpace *> pExpr <* pWhiteSpace)
    where
        f :: Expr -> [Expr] -> Expr
        f e1 [] = e1
        f e1 es = Seq (e1 : es)

pLet :: Parsec String () Expr
pLet = Let
    <$> (string "let" *> pWhiteSpace *> (extractVar <$> pVar))
    <*> (pWhiteSpace *> char ':' *> pWhiteSpace *> pTipo)
    <*> (pWhiteSpace *> string ":=" *> pWhiteSpace *> pExpr)
    where
        extractVar :: Expr -> String
        extractVar (Var s) = s
        extractVar _ = error "Expected a variable"

pAssign :: Parsec String () Expr
pAssign = Assign
    <$> (extractVar <$> pVar)
    <*> (pWhiteSpace *> string ":=" *> pWhiteSpace *> pExpr)
    where
        extractVar :: Expr -> String
        extractVar (Var s) = s
        extractVar _ = error "Expected a variable"

pPrint :: Parsec String () Expr
pPrint = Print <$> (string "print" *> pWhiteSpace *> pExpr)

pExpr :: Parsec String () Expr
pExpr = buildExpressionParser table (try pApp <|> pExpr')
    where
        table =
            [ [ Infix  (Operation Exp <$ try (pWhiteSpace *> char '^' <* pWhiteSpace)) AssocRight ]
            , [ Infix  (Operation Mul <$ try (pWhiteSpace *> char '*' <* pWhiteSpace)) AssocLeft
              , Infix  (Operation Div <$ try (pWhiteSpace *> char '/' <* pWhiteSpace)) AssocLeft ]
            , [ Prefix (Neg <$ try (pWhiteSpace *> char '-')) ]
            , [ Infix  (Operation Add <$ try (pWhiteSpace *> char '+' <* pWhiteSpace)) AssocLeft
              , Infix  (Operation Sub <$ try (pWhiteSpace *> char '-' <* pWhiteSpace)) AssocLeft ]
            ]

pExpr' :: Parsec String () Expr
pExpr' = pWhiteSpace *>
    (   pBoolean
    <|> pNumber
    <|> try pLambda
    <|> try pIf
    <|> try pLet
    <|> try pAssign
    <|> try pVar
    <|> try pPrint
    <|> between (char '(') (char ')') pSeq
    )

data Value
    = VNum Double
    | VBool Bool
    | VFun Expr (Value -> EvalMonad Value)

instance Show Value where
    show (VNum n)   = show n
    show (VBool b)  = if b then "true" else "false"
    show (VFun e _) = show e

type Env = Map String (MVar Value)

newtype EvalMonad a = MkEvalMonad
    { runEvalMonad :: ReaderT Env (ExceptT String IO) a
    } deriving newtype
        ( Functor
        , Applicative
        , Monad
        , MonadIO
        , MonadReader Env
        , MonadError String
        )

fully :: Parsec String () a -> Parsec String () a
fully p = p <* pWhiteSpace <* eof

initialEnv :: IO Env
initialEnv = return Map.empty

eval :: Expr -> EvalMonad Value
eval (Num n)     = return (VNum n)
eval (Boolean b) = return (VBool b)
eval (Var x)     = do
    env <- ask
    case Map.lookup x env of
        Nothing   -> throwError $ "Variable not in scope: " ++ x
        Just mvar -> liftIO $ readMVar mvar
eval (Neg e) = do
    v <- eval e
    case v of
        VNum n -> return (VNum (-n))
        _      -> throwError "Type error in minus: expected R"
eval (Operation op e1 e2) = do
    v1 <- eval e1
    v2 <- eval e2
    case (v1, v2) of
        (VNum n1, VNum n2) -> return $ VNum $ case op of
            Add -> n1 + n2
            Sub -> n1 - n2
            Mul -> n1 * n2
            Div -> n1 / n2
            Exp -> n1 ** n2
        _ -> throwError "Type error in arithmetic operation"
eval (If cond e1 e2) = do
    v <- eval cond
    case v of
        VBool True  -> eval e1
        VBool False -> eval e2
        VNum 0.0    -> eval e2
        VNum _      -> eval e1
        _           -> throwError "Type error in if condition"
eval (Lambda x t e) = do
    currentEnv <- ask
    let f v = do
            mvar <- liftIO $ newMVar v
            local (const $ Map.insert x mvar currentEnv) (eval e)
    return $ VFun (Lambda x t e) f
eval (App e1 e2) = do
    f <- eval e1
    v <- eval e2
    case f of
        VFun _ g -> g v
        _        -> throwError "Type error: expected a function"
eval (Print e) = do
    v <- eval e
    liftIO $ putStrLn (show v)
    return v
eval (Assign x e) = do
    env <- ask
    v   <- eval e
    case Map.lookup x env of
        Nothing   -> throwError $ "Variable not in scope: " ++ x
        Just mvar -> do
            liftIO $ takeMVar mvar
            liftIO $ putMVar mvar v
            return v
eval (Let x _ e) = do
    mvar <- liftIO newEmptyMVar
    v    <- local (Map.insert x mvar) (eval e)
    liftIO $ putMVar mvar v
    return v
eval (Seq es)    = evalSeq es
  where
    evalSeq []                    = throwError "Empty sequence"
    evalSeq [x]                   = eval x
    evalSeq (Let var _ e : rest)  = do
        mvar <- liftIO newEmptyMVar
        local (Map.insert var mvar) $ do
            v <- eval e
            liftIO $ putMVar mvar v
            evalSeq rest
    evalSeq (x : rest)            = do
        eval x
        evalSeq rest

runInterpreter :: String -> IO ()
runInterpreter s = case runParser (fully pSeq) () "" s of
    Left pError -> print pError
    Right pe    -> case typeCheck Map.empty pe of
        Left tError -> putStrLn tError
        Right _     -> do
            env <- initialEnv
            runExceptT (runReaderT (runEvalMonad (eval pe)) env) >>= \case
                Left xError -> putStrLn xError
                Right _     -> return ()

runL :: FilePath -> IO ()
runL filePath = readFile filePath >>= runInterpreter
