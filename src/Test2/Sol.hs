module Test2.Sol where

import Text.Parsec
import Data.Map (Map)
import Data.Map qualified as Map
import Data.List (intercalate)

-- Leonardo López 25-91752
-- Carla Gómez 25-91750

data Tipo = TNum
          | TBool
          | TFun Tipo Tipo
          deriving (Eq)

instance Show Tipo where
    show TNum = "R"
    show TBool = "B"
    show (TFun t1 t2) = show t1 ++ " -> " ++ show t2

data Operator = Add | Sub | Mul | Div | Exp
    deriving (Eq)

instance Show Operator where
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
          | Operation Operator Expr Expr
          deriving (Eq)

instance Show Expr where
    show (Var x) = x
    show (Lambda x t e) = "/. " ++ x ++ " : " ++ show t ++ " => " ++ show e
    show (App e1 e2) = show e1 ++ " " ++ show e2
    show (If e1 e2 e3) = "if " ++ show e1 ++ " then " ++ show e2 ++ " else " ++ show e3
    show (Seq es) = intercalate "; " $ map show es
    show (Let x t e) = "let " ++ x ++ " : " ++ show t ++ " := " ++ show e
    show (Assign x e) = x ++ " := " ++ show e
    show (Num n) = show n
    show (Boolean b) = if b then "true" else "false"
    show (Print e) = "print " ++ show e
    show (Operation op e1 e2) = show e1 ++ " " ++ show op ++ " " ++ show e2

typeCheck :: Map String Tipo -> Expr -> Either String Tipo
typeCheck env (Var x) = case Map.lookup x env of
        Just t -> Right t
        Nothing -> Left $ "Variable " ++ x ++ " not declared"
typeCheck env (Lambda x t e) = case typeCheck (Map.insert x t env) e of
        Right t' -> Right $ TFun t t'
        Left err -> Left err
typeCheck env (App e1 e2) = case (t1, t2) of
    (Right (TFun argType retType), Right t2') -> if argType == t2'
        then Right retType
        else Left $ "Type mismatch: expected " ++ show argType ++ ", found " ++ show t2'
    (Right t1', _) -> Left $ "Type error: expected a function, found " ++ show t1'
    (Left err, _) -> Left err
    (_, Left err) -> Left err
    where
        t1 = typeCheck env e1
        t2 = typeCheck env e2
typeCheck env (If cond block1 block2) = case typeCheck env cond of
    Right TBool -> case (typeCheck env block1, typeCheck env block2) of
        (Right t1, Right t2) -> if t1 == t2
            then Right t1
            else Left $ "Type mismatch in branches: " ++ show t1 ++ " and " ++ show t2
        (Left err, _) -> Left err
        (_, Left err) -> Left err
    Right t -> Left $ "Type error: expected B, found " ++ show t
    Left err -> Left err
typeCheck env (Seq es) = laMalandra env es
    where 
        laMalandra env [x] = case typeCheck env x of
            Right t -> Right t
            Left err -> Left err
        laMalandra env (x:xs) = case x of
            Let var t e -> case typeCheck env e of
                Right t' -> if t == t'
                    then laMalandra (Map.insert var t env) xs
                    else Left $ "Type mismatch in let: declared " ++ show t ++ ", found " ++ show t'
                Left err -> Left err
            e -> case typeCheck env e of
                Right _ -> laMalandra env xs
                Left err -> Left err
        laMalandra env [] = Right TBool -- Shouldn't be reachable anyway
typeCheck env (Let x t e) = case typeCheck env e of
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
typeCheck env (Operation op e1 e2) = case (typeCheck env e1, typeCheck env e2) of
    (Right TNum, Right TNum) -> Right TNum
    (Right t1, Right t2) -> Left $ "Type error in operation: expected R and R, found " ++ show t1 ++ " and " ++ show t2
    (Left err, _) -> Left err
    (_, Left err) -> Left err

runL :: FilePath -> IO ()
runL = undefined
