module Test1.Sol where

import Data.List (intercalate, inits, tails, nub)
import Data.Char (toLower, isSpace)
import Data.Either (isRight)
import Control.Monad
import Control.Applicative
import Control.Monad.Free
import Debug.Trace
import Data.Map (Map)
import qualified Data.Map as Map
import Data.Set (Set)
import qualified Data.Set as Set
import Control.Monad.State
import Control.Monad.Reader
import Data.Maybe
import Control.Monad.Except
import Data.Traversable
import Data.Foldable

------------------------
--- 1.
------------------------

newtype AccountId = AccountId String deriving (Show, Eq, Ord)
newtype User = User String deriving (Show, Eq)
data Error = InsufficientFunds | AccountNotFound deriving (Show, Eq)

data ATMF a
    = CheckBalance AccountId (Int -> a)
    | Deposit AccountId Int a
    | Withdraw AccountId Int (Either Error a)
    | GetUser AccountId (Maybe User -> a)

instance Functor ATMF where
    fmap f (CheckBalance acc g) = CheckBalance acc (f . g)
    fmap f (Deposit acc amount a) = Deposit acc amount (f a)
    fmap f (Withdraw acc amount a) = Withdraw acc amount (fmap f a)
    fmap f (GetUser acc g) = GetUser acc (f . g)

{- 
Proving this implementation satisfies the functor laws:

1. Identity: fmap id = id
fmap id (CheckBalance acc g) = CheckBalance acc (id . g) = CheckBalance acc g
fmap id (Deposit acc amount a) = Deposit acc amount (id a) = Deposit acc amount a
fmap id (Withdraw acc amount a) = Withdraw acc amount (fmap id a) = Withdraw acc amount a
fmap id (GetUser acc g) = GetUser acc (id . g) = GetUser acc g
In each case, fmap id behaves as id

2. Composition: fmap (f . g) = fmap f . fmap g

fmap (f . g) (CheckBalance acc h) = CheckBalance acc ((f . g) . h)
fmap f (fmap g (CheckBalance acc h)) = fmap f (CheckBalance acc (g . h)) = CheckBalance acc (f . (g . h))
Since (f . g) . h = f . (g . h), the composition law holds in this case

fmap (f . g) (GetUser acc h) = GetUser acc ((f . g) . h) = GetUser acc (f . (g . h))
fmap f (fmap g (GetUser acc h)) = fmap f (GetUser acc (g . h)) = GetUser acc (f . (g . h))
Since (f . g) . h = f . (g . h), the composition law holds in this case

fmap (f . g) (Deposit acc amount a) = Deposit acc amount ((f . g) a)
fmap f (fmap g (Deposit acc amount a)) = fmap f (Deposit acc amount (g a)) = Deposit acc amount (f (g a))
Since (f . g) a = f (g a), the composition law holds in this case

fmap (f . g) (Withdraw acc amount a) = Withdraw acc amount (fmap (f . g) a)
fmap f (fmap g (Withdraw acc amount a)) = fmap f (Withdraw acc amount (fmap g a))
    = Withdraw acc amount (fmap f (fmap g a))
Since a is of type Either Error a, and Either is a functor, it holdas that fmap (f . g) a = fmap f (fmap g a)
Therefore, the composition law holds in this case
-}

checkBalance :: AccountId -> Free ATMF Int
checkBalance acc = liftF (CheckBalance acc id)

deposit :: AccountId -> Int -> Free ATMF ()
deposit acc amount = liftF (Deposit acc amount ())

withdraw :: AccountId -> Int -> Free ATMF (Either Error ())
withdraw acc amount = liftF (Withdraw acc amount (Right $ Right ()))

getUser :: AccountId -> Free ATMF (Maybe User)
getUser acc = liftF (GetUser acc id)

transfer :: AccountId -> AccountId -> Int -> Free ATMF (Either Error ())
transfer from to amount = do
    fromUser <- getUser from
    toUser <- getUser to
    case (fromUser, toUser) of
        (Nothing, _) -> pure $ Left AccountNotFound
        (_, Nothing) -> pure $ Left AccountNotFound
        (Just _, Just _) -> do
            balance <- checkBalance from
            withdrawResult <- withdraw from amount
            case withdrawResult of
                Left err -> pure $ Left err
                Right () -> do
                    deposit to amount
                    pure $ Right ()

{-
Implementing transfer' with the given signature is not possible because it would require
the Left case to have knowledge of the monadic state in a pure context, which is not allowed

The following example illustrates why this is the case:

transfer' :: AccountId -> AccountId -> Int -> Either Error (Free ATMF ())
transfer' from to amount = let userResult = getUser from 
    in case userResult of
        Nothing -> Left AccountNotFound

The above code will result in a type error
    Couldn't match expected type: Free ATMF (Maybe User)
                with actual type: Maybe a0
This is because getUser from returns a Free ATMF (Maybe User), so the Nothing or Just value is
wrapped inside the monadic context we can't access.

See transfer'' for an implementation that uses an BankEnv typeclass to provide the necessary information
this is essentially equivalent to assuming we have access to a BankState object and we can access it purely
-}

transfer' :: AccountId -> AccountId -> Int -> Either Error (Free ATMF ())
transfer' from to amount = undefined

class BankEnv where
    isRegisteredPure :: AccountId -> Bool
    checkBalancePure :: AccountId -> Maybe Int

transfer'' :: (BankEnv) => AccountId -> AccountId -> Int -> Either Error (Free ATMF ())
transfer'' from to amount
    | not (isRegisteredPure from) = Left AccountNotFound
    | not (isRegisteredPure to)   = Left AccountNotFound
    | fromMaybe 0 (checkBalancePure from) < amount = Left InsufficientFunds
    | otherwise                   = Right $ do
        withdrawResult <- withdraw from amount
        case withdrawResult of
            Left err -> liftF $ Withdraw from 0 (Left err)
            Right _  -> deposit to amount

accountIds :: Free ATMF a -> [AccountId]
accountIds program = nub $ accountIds' program -- eliminates duplicates

accountIds' :: Free ATMF a -> [AccountId]
accountIds' program = case program of
    Pure _ -> []
    Free (CheckBalance acc next) -> acc : accountIds (next 0)
    Free (Deposit acc _ next) -> acc : accountIds next
    Free (Withdraw acc _ next) -> acc : case next of
        Left err -> []
        Right nextProgram -> accountIds nextProgram
    Free (GetUser acc next) -> acc : accountIds (next Nothing)

newtype BankState = MkBankState (Map AccountId (Int, User)) deriving (Show)

interpret :: Free ATMF a -> BankState -> (Either Error a, BankState)
interpret program state = case program of
    Pure a -> (Right a, state)
    Free (CheckBalance acc next) -> if Map.member acc accounts
        then interpret (next balance) state
        else (Left AccountNotFound, state)
      where
        MkBankState accounts = state
        balance = fst $ fromMaybe (0, undefined) $ Map.lookup acc accounts
    Free (Deposit acc amount next) -> if Map.member acc accounts
        then interpret next newState
        else (Left AccountNotFound, state)
      where
        MkBankState accounts = state
        (prevBalance, user) = fromMaybe (0, undefined) $ Map.lookup acc accounts
        newState = MkBankState $ Map.insert acc (prevBalance + amount, user) accounts
    Free (Withdraw acc amount next) -> if Map.member acc accounts
        then if prevBalance < amount
            then (Left InsufficientFunds, state)
            else case next of
                Left err -> (Left err, state)
                Right nextProgram -> interpret nextProgram newState
        else (Left AccountNotFound, state)
      where
        MkBankState accounts = state
        (prevBalance, user) = fromMaybe (0, undefined) $ Map.lookup acc accounts
        newState = MkBankState $ Map.insert acc (prevBalance - amount, user) accounts
    Free (GetUser acc next) -> if Map.member acc accounts
        then interpret (next (Just user)) state
        else interpret (next Nothing) state
      where
        MkBankState accounts = state
        (_, user) = fromMaybe (0, undefined) $ Map.lookup acc accounts

testBankState :: BankState
testBankState = MkBankState $ Map.fromList
    [ (AccountId "acc1", (100, User "Wilkerman"))
    , (AccountId "acc2", (50, User "Yuruski"))
    ]

testProgram1 :: Free ATMF (Either Error ())
testProgram1 = transfer (AccountId "acc1") (AccountId "acc2") 50

testProgram2 :: Free ATMF (Either Error ())
testProgram2 = transfer (AccountId "acc1") (AccountId "acc2") 150

testProgram3 :: Free ATMF (Either Error ())
testProgram3 = do
    transfer (AccountId "acc1") (AccountId "acc2") 50
    transfer (AccountId "acc1") (AccountId "acc2") 50

-------------------------
--- 2.
-------------------------

type Weight = Int
newtype Graph a = Graph [(a,[(Weight,a)])]

paths :: forall a. Ord a => a -> Graph a -> [[a]]
paths v graph = runReader (paths' v graph) Set.empty

paths' :: forall a. Ord a => a -> Graph a -> Reader (Set a) [[a]]
paths' v graph = do
    visited <- ask
    if Set.member v visited
        then pure []
        else do
            let adjacent = fromMaybe [] $ lookup v edges
            subPaths <- local (Set.insert v) $
                            forM adjacent $ \(_, u) -> paths' u graph
            pure $ [v] : concatMap (map (v:)) subPaths
  where
    Graph edges = graph

{-
I chose Reader over State because the visited set should be read only
If using State, it would be necessary to manually save and restore for every branch.
The local function handles this automatically.
-}

testGraph :: Graph Char
testGraph = Graph
    [ ('A', [(1, 'B'), (4, 'C')])
    , ('B', [(2, 'D')])
    , ('C', [(3, 'D')])
    , ('D', [(4, 'C')])
    ]

--------------------------
--- 3.
--------------------------


data MyExceptT e m a = MyExceptT { runMyExceptT :: m (Either e a) }

instance Functor m => Functor (MyExceptT e m) where
    fmap :: (a -> b) -> MyExceptT e m a -> MyExceptT e m b
    fmap f (MyExceptT ma) = MyExceptT $ fmap (fmap f) ma

instance Applicative m => Applicative (MyExceptT e m) where
    pure :: a -> MyExceptT e m a
    pure = MyExceptT . pure . Right
    (<*>) :: MyExceptT e m (a -> b) -> MyExceptT e m a -> MyExceptT e m b
    (<*>) (MyExceptT mf) (MyExceptT ma) = MyExceptT $ fmap (<*>) mf <*> ma

instance Monad m => Monad (MyExceptT e m) where
    (>>=) :: MyExceptT e m a -> (a -> MyExceptT e m b) -> MyExceptT e m b
    (>>=) (MyExceptT ma) f = MyExceptT $ do
        result <- ma
        case result of
            Left err -> pure $ Left err
            Right val -> runMyExceptT (f val)

testMyExceptT :: String -> IO (Either String Int)
testMyExceptT input = runMyExceptT $ case reads input of
    [(n, "")] -> if n < 0
        then MyExceptT $ pure $ Left "No me sirve negativo chico"
        else pure n
    _ -> MyExceptT $ pure $ Left $ "No me sirve " ++ input ++ " chico"

--------------------------
--- 4.
--------------------------

data PieceType = Pawn | Knight | Bishop | Rook | Queen | King deriving (Eq, Show, Read)
data Piece = Piece
    { pieceType :: PieceType
    , pieceColor :: Color
    } deriving (Eq)
data Color = White | Black deriving (Eq, Show)
data Position = Position
    { rank :: Int
    , file :: Char
    } deriving (Eq,Ord)
instance Show Position where
    show (Position r f) = show r ++ [f]
data Move = Move
    { from :: Position
    , to   :: Position
    } deriving (Eq, Show)

data Move' = Regular Move | Castle Bool deriving (Show)

newtype Board = MkBoard (Map Position Piece)

data BoardState' a = BoardState'
    { board       :: Board
    , turn        :: Color
    , customState :: a
    }

data CastlingAllowed = CastlingAllowed
    { whiteKingside  :: Bool
    , whiteQueenside :: Bool
    , blackKingside  :: Bool
    , blackQueenside :: Bool
    } deriving (Eq, Show)

data AdditionalState = AdditionalState
    { castlingAllowed :: CastlingAllowed
    , enPassantTarget :: Maybe Position
    } deriving (Eq, Show)
type BoardState = BoardState' AdditionalState

data BoardError
    = InvalidMove { reasonIM :: String }

instance Show BoardError where
    show (InvalidMove reason) = reason

initialState :: BoardState
initialState = BoardState'
    { board = MkBoard $ Map.fromList $
        [ (Position 1 'a', Piece Rook White)
        , (Position 1 'b', Piece Knight White)
        , (Position 1 'c', Piece Bishop White)
        , (Position 1 'd', Piece Queen White)
        , (Position 1 'e', Piece King White)
        , (Position 1 'f', Piece Bishop White)
        , (Position 1 'g', Piece Knight White)
        , (Position 1 'h', Piece Rook White)
        ] ++ [ (Position 2 col, Piece Pawn White) | col <- ['a'..'h'] ]
          ++ [ (Position 7 col, Piece Pawn Black) | col <- ['a'..'h'] ]
          ++ 
        [ (Position 8 'a', Piece Rook Black)
        , (Position 8 'b', Piece Knight Black)
        , (Position 8 'c', Piece Bishop Black)
        , (Position 8 'd', Piece Queen Black)
        , (Position 8 'e', Piece King Black)
        , (Position 8 'f', Piece Bishop Black)
        , (Position 8 'g', Piece Knight Black)
        , (Position 8 'h', Piece Rook Black)
        ]
    , turn = White
    , customState = AdditionalState
        { castlingAllowed = CastlingAllowed True True True True
        , enPassantTarget = Nothing
        }
    }

toString' :: BoardState -> String
toString' = toString . board

toString :: Board -> String
toString (MkBoard pieces) = intercalate "\n" (header : map renderRow [8,7..1] ++ [header])
  where
    header = "    a b c d e f g h"

    renderRow :: Int -> String
    renderRow r =
        let cells = [pieceAt r f | f <- ['a'..'h']]
        in show r ++ " | " ++ intercalate " " cells ++ " | " ++ show r

    pieceAt :: Int -> Char -> String
    pieceAt r f = case Map.lookup (Position r f) pieces of
        Nothing -> "-"
        Just p -> [pieceSymbol p]

    pieceSymbol :: Piece -> Char
    pieceSymbol (Piece Pawn Black) = '♙'
    pieceSymbol (Piece Knight Black) = '♘'
    pieceSymbol (Piece Bishop Black) = '♗'
    pieceSymbol (Piece Rook Black) = '♖'
    pieceSymbol (Piece Queen Black) = '♕'
    pieceSymbol (Piece King Black) = '♔'
    pieceSymbol (Piece Pawn White) = '♟'
    pieceSymbol (Piece Knight White) = '♞'
    pieceSymbol (Piece Bishop White) = '♝'
    pieceSymbol (Piece Rook White) = '♜'
    pieceSymbol (Piece Queen White) = '♛'
    pieceSymbol (Piece King White) = '♚'

isLegalPieceMove :: BoardState -> Move -> Piece -> Bool
isLegalPieceMove boardState move movingPiece =
    case pieceType movingPiece of
        Pawn   -> validPawnMove (pieceColor movingPiece)
        Knight -> elem (absDifRow, absDifCol) [(2,1), (1,2)]
        Bishop -> absDifRow == absDifCol && absDifRow /= 0 && clearPath (signum difRow) (signum difCol)
        Rook   -> (difRow /= 0 && difCol == 0 && clearPath (signum difRow) 0)
               || (difRow == 0 && difCol /= 0 && clearPath 0 (signum difCol))
        Queen  -> (absDifRow == absDifCol && absDifRow /= 0 && clearPath (signum difRow) (signum difCol))
               || (difRow == 0 && absDifCol /= 0 && clearPath 0 (signum difCol))
               || (difCol == 0 && absDifRow /= 0 && clearPath (signum difRow) 0)
        King   -> max absDifRow absDifCol == 1
  where
    MkBoard pieces = board boardState
    extraState = customState boardState
    epTarget = enPassantTarget extraState
    Position r1 f1 = from move
    Position r2 f2 = to move
    difRow = r2 - r1
    difCol = fromEnum f2 - fromEnum f1
    absDifRow = abs difRow
    absDifCol = abs difCol
    targetPiece = Map.lookup (to move) pieces
    isTargetEmpty = isNothing targetPiece

    isCapture :: Bool
    isCapture = maybe False ((/= pieceColor movingPiece) . pieceColor) targetPiece

    validPawnMove :: Color -> Bool
    validPawnMove White =
        (difCol == 0 && difRow == 1 && isTargetEmpty) ||
        (difCol == 0 && difRow == 2 && r1 == 2 && isTargetEmpty && isNothing (Map.lookup (Position 3 f1) pieces)) ||
        (absDifCol == 1 && difRow == 1 && (isCapture || isEnPassantCapture))
    validPawnMove Black =
        (difCol == 0 && difRow == -1 && isTargetEmpty) ||
        (difCol == 0 && difRow == -2 && r1 == 7 && isTargetEmpty && isNothing (Map.lookup (Position 6 f1) pieces)) ||
        (absDifCol == 1 && difRow == -1 && (isCapture || isEnPassantCapture))

    isEnPassantCapture :: Bool
    isEnPassantCapture = isTargetEmpty && epTarget == Just (to move)

    clearPath :: Int -> Int -> Bool
    clearPath rowSign colSign =
        let steps = max absDifRow absDifCol - 1
            positions = [Position (r1 + i * rowSign) (toEnum (fromEnum f1 + i * colSign)) | i <- [1..steps]]
        in all (`Map.notMember` pieces) positions

applyMove :: BoardState -> Move -> Either BoardError BoardState
applyMove boardState move =
    case Map.lookup (from move) pieces of
        Nothing -> Left $ InvalidMove "No piece at the 'from' position"
        Just movingPiece
            | pieceColor movingPiece /= turn boardState ->
                Left $ InvalidMove $ "It's " ++ show (turn boardState) ++ "'s turn"
            | isSelfCapture movingPiece ->
                Left $ InvalidMove "Can't take your own piece"
            | not (isLegalPieceMove boardState move movingPiece) ->
                Left $ InvalidMove $ (show $ pieceType movingPiece) ++ "s can't move like that"
            | inCheck (turn boardState) newState ->
                Left $ InvalidMove "Can't make a move that leaves you in check"
            | otherwise ->
                Right newState
          where
            newBoard = MkBoard $ Map.insert (to move) movingPiece $ Map.delete (from move) $
                if isEnPassantCapture
                    then Map.delete (Position r1 f2) pieces
                    else pieces
            nextTurn = case turn boardState of
                White -> Black
                Black -> White
            updatedCastlingData = updateCastlingData (castlingAllowed extraState) movingPiece (from move) (to move) targetPiece
            updatedEnPassantTarget = case pieceType movingPiece of
                Pawn | absDifRow == 2 -> Just (Position (r1 + signum difRow) f1)
                _ -> Nothing
            newCustomState = AdditionalState
                { castlingAllowed = updatedCastlingData
                , enPassantTarget = updatedEnPassantTarget
                }
            newState = boardState
                { board = newBoard
                , turn = nextTurn
                , customState = newCustomState
                }

    where
        MkBoard pieces = board boardState
        extraState = customState boardState
        epTarget = enPassantTarget extraState
        Position r1 f1 = from move
        Position r2 f2 = to move
        difRow = r2 - r1
        difCol = fromEnum f2 - fromEnum f1
        absDifRow = abs difRow
        absDifCol = abs difCol
        targetPiece = Map.lookup (to move) pieces
        isTargetEmpty = isNothing targetPiece

        isSelfCapture :: Piece -> Bool
        isSelfCapture movingPiece = case Map.lookup (to move) pieces of
            Just targetPiece -> pieceColor targetPiece == pieceColor movingPiece
            Nothing -> False

        isEnPassantCapture :: Bool
        isEnPassantCapture = isTargetEmpty && epTarget == Just (to move)

        updateCastlingData :: CastlingAllowed -> Piece -> Position -> Position -> Maybe Piece -> CastlingAllowed
        updateCastlingData prevData movingPiece fromPos toPos capturedPiece =
            applyCaptureCastling toPos capturedPiece $ applyMoveCastling fromPos movingPiece prevData
          where
            applyMoveCastling :: Position -> Piece -> CastlingAllowed -> CastlingAllowed
            applyMoveCastling (Position 1 'e') (Piece King White) r = r { whiteKingside = False, whiteQueenside = False }
            applyMoveCastling (Position 8 'e') (Piece King Black) r = r { blackKingside = False, blackQueenside = False }
            applyMoveCastling (Position 1 'h') (Piece Rook White) r = r { whiteKingside = False }
            applyMoveCastling (Position 1 'a') (Piece Rook White) r = r { whiteQueenside = False }
            applyMoveCastling (Position 8 'h') (Piece Rook Black) r = r { blackKingside = False }
            applyMoveCastling (Position 8 'a') (Piece Rook Black) r = r { blackQueenside = False }
            applyMoveCastling _ _ r = r

            applyCaptureCastling :: Position -> Maybe Piece -> CastlingAllowed -> CastlingAllowed
            applyCaptureCastling (Position 1 'h') (Just (Piece Rook White)) r = r { whiteKingside = False }
            applyCaptureCastling (Position 1 'a') (Just (Piece Rook White)) r = r { whiteQueenside = False }
            applyCaptureCastling (Position 8 'h') (Just (Piece Rook Black)) r = r { blackKingside = False }
            applyCaptureCastling (Position 8 'a') (Just (Piece Rook Black)) r = r { blackQueenside = False }
            applyCaptureCastling _ _ r = r

triggersPromotion :: Move -> BoardState -> Bool
triggersPromotion (Move from (Position row _)) boardState =
    case Map.lookup from pieces of
        Just (Piece Pawn color) -> (color == White && row == 8) || (color == Black && row == 1)
        _ -> False
  where
    MkBoard pieces = board boardState

applyPromotion :: Position -> PieceType -> BoardState -> BoardState
applyPromotion pos newType boardState =
    case Map.lookup pos pieces of
        Just (Piece Pawn color) -> boardState
            { board = MkBoard $ Map.insert pos (Piece newType color) pieces }
        _ -> boardState
  where
    MkBoard pieces = board boardState

promotionPrompt :: Position -> StateT BoardState (ExceptT BoardError IO) ()
promotionPrompt pos = do
    boardState <- get
    liftIO $ putStrLn "Pawn promotion triggered. Enter piece type (Queen, Rook, Bishop, Knight):"
    input <- liftIO getLine
    case reads input of
        [(newType, "")] | elem newType [Queen, Rook, Bishop, Knight] -> do
            let promotedState = applyPromotion pos newType boardState
            put promotedState
        _ -> do
            liftIO $ putStrLn "Invalid piece type. Please try again."
            promotionPrompt pos

applyMove' :: Move' -> BoardState -> Either BoardError BoardState
applyMove' (Regular move) boardState = applyMove boardState move
applyMove' (Castle queenSide) boardState = applyCastles (turn boardState) queenSide boardState

validMoves :: BoardState -> [Move]
validMoves boardState = [
    Move from to
        | from <- allPositions
        , to <- allPositions
        , isRight (applyMove boardState (Move from to))
    ]
    where
        allPositions = [Position r f | r <- [1..8], f <- ['a'..'h']]

inCheck :: Color -> BoardState -> Bool
inCheck color boardState =
    case kingPos of
        Nothing -> False
        Just kp -> any (attacksKing kp) enemyPieces
  where
    MkBoard pieces = board boardState
    kingPos = fmap fst $ find (\(_, p) -> pieceType p == King && pieceColor p == color) (Map.toList pieces)
    enemyPieces = [ (pos, p) | (pos, p) <- Map.toList pieces, pieceColor p /= color ]

    attacksKing kp (fromPos, attacker) =
        isLegalPieceMove boardState (Move fromPos kp) attacker

inCheckmate :: BoardState -> Bool
inCheckmate boardState =
    inCheck (turn boardState) boardState && (validMoves boardState) == []

applyCastles :: Color -> Bool -> BoardState -> Either BoardError BoardState
applyCastles color queenSide boardState
    | color /= turn boardState = Left $ InvalidMove $ "It's " ++ show (turn boardState) ++ "'s turn"
    | inCheck color boardState = Left $ InvalidMove "Can't castle while in check"
    | not canCastle = Left $ InvalidMove "Can't castle because of previous moves"
    | not pathClear = Left $ InvalidMove "Can't castle because there are pieces on the way"
    | inCheck color (boardState { board = MkBoard newBoard }) = Left $ InvalidMove "Can't make a move that leaves you in check"
    | otherwise = Right $ newState
    where
        MkBoard pieces = board boardState
        canCastle = case color of
            White -> if queenSide 
                then whiteQueenside (castlingAllowed extraState) 
                else whiteKingside (castlingAllowed extraState)
            Black -> if queenSide 
                then blackQueenside (castlingAllowed extraState) 
                else blackKingside (castlingAllowed extraState)
        pathClear = case color of
            White -> if queenSide 
                then all (`Map.notMember` pieces) [Position 1 'b', Position 1 'c', Position 1 'd']
                else all (`Map.notMember` pieces) [Position 1 'f', Position 1 'g']
            Black -> if queenSide 
                then all (`Map.notMember` pieces) [Position 8 'b', Position 8 'c', Position 8 'd']
                else all (`Map.notMember` pieces) [Position 8 'f', Position 8 'g']
        extraState = customState boardState
        newBoard = case color of
            White -> if queenSide
                then let b1 = Map.delete (Position 1 'e') pieces
                         b2 = Map.delete (Position 1 'a') b1
                         b3 = Map.insert (Position 1 'c') (Piece King White) b2
                     in Map.insert (Position 1 'd') (Piece Rook White) b3
                else let b1 = Map.delete (Position 1 'e') pieces
                         b2 = Map.delete (Position 1 'h') b1
                         b3 = Map.insert (Position 1 'g') (Piece King White) b2
                     in Map.insert (Position 1 'f') (Piece Rook White) b3
            Black -> if queenSide
                then let b1 = Map.delete (Position 8 'e') pieces
                         b2 = Map.delete (Position 8 'a') b1
                         b3 = Map.insert (Position 8 'c') (Piece King Black) b2
                     in Map.insert (Position 8 'd') (Piece Rook Black) b3
                else let b1 = Map.delete (Position 8 'e') pieces
                         b2 = Map.delete (Position 8 'h') b1
                         b3 = Map.insert (Position 8 'g') (Piece King Black) b2
                     in Map.insert (Position 8 'f') (Piece Rook Black) b3
        newCastlingData = case color of
            White -> if queenSide
                then (castlingAllowed extraState) { whiteQueenside = False, whiteKingside = False }
                else (castlingAllowed extraState) { whiteKingside = False, whiteQueenside = False }
            Black -> if queenSide
                then (castlingAllowed extraState) { blackQueenside = False, blackKingside = False }
                else (castlingAllowed extraState) { blackKingside = False, blackQueenside = False }
        newCustomState = extraState { castlingAllowed = newCastlingData, enPassantTarget = Nothing }
        newState = boardState
            { board = MkBoard newBoard
            , turn = if turn boardState == White then Black else White
            , customState = newCustomState
            }

move :: Move -> StateT BoardState (ExceptT BoardError IO) ()
move (Move from to) = do
    boardState <- get
    case applyMove boardState (Move from to) of
        Left err -> lift $ throwError err
        Right newState -> do
            liftIO $ putStrLn $ "Move made: " ++ show from ++ " to " ++ show to
            put newState
            when (triggersPromotion (Move from to) boardState) $ do
                promotionPrompt to

move' :: Move' -> StateT BoardState (ExceptT BoardError IO) ()
move' (Regular m) = move m
move' (Castle queenSide) = do
    boardState <- get
    case applyCastles (turn boardState) queenSide boardState of
        Left err -> lift $ throwError err
        Right newState -> do
            put newState
            liftIO $ putStrLn "Castling performed"

parseMove :: String -> Either BoardError Move'
parseMove input = case map toLower $ filter (not . isSpace) input of
    "o-o-o" -> Right $ Castle True
    "o-o"   -> Right $ Castle False
    [col1, row1, col2, row2] ->
        case (reads [row1], reads [row2]) of
            ([(r1, "")], [(r2, "")]) -> Right $ Regular $ Move (Position r1 col1) (Position r2 col2)
            _ -> Left $ InvalidMove "Invalid move format"
    _ -> Left $ InvalidMove "Invalid move format"

handler :: BoardError -> StateT BoardState (ExceptT BoardError IO) ()
handler err = do
    liftIO $ putStrLn $ "Error: " ++ show err ++ ". Please try again."
    gameLoop

gameLoop :: StateT BoardState (ExceptT BoardError IO) ()
gameLoop = catchError gameLoop' handler
    where
        gameLoop' = do
            printState
            boardState <- get
            liftIO $ putStrLn $ "Enter move for " ++ (show $ turn boardState) ++ "s:"
            input <- liftIO getLine
            case parseMove input of
                Left err -> do
                    liftIO $ putStrLn $ "Parsing Error: " ++ show err ++ ". Please try again."
                    gameLoop
                Right m -> do
                    move' m
                    newState <- get
                    if inCheckmate newState
                        then do
                            printState
                            let winner = case turn newState of
                                    White -> Black
                                    Black -> White
                            liftIO $ putStrLn $ "CHECKMATE " ++ show winner ++ " WINS"
                        else do 
                            when (inCheck (turn newState) newState) $
                                    liftIO $ putStrLn $ "CHECK for " ++ show (turn newState)
                            gameLoop

playGame :: StateT BoardState (ExceptT BoardError IO) ()
playGame = do
    put initialState
    gameLoop

playChess :: IO ()
playChess = runExceptT (runStateT playGame initialState) >>= \case
    Left err -> putStrLn $ "Game ended with error: " ++ show err
    Right _ -> putStrLn "Game ended successfully"

printState :: StateT BoardState (ExceptT BoardError IO) ()
printState = do
    state <- get
    liftIO $ putStrLn $ toString' state

testChess :: StateT BoardState (ExceptT BoardError IO) ()
testChess = do
    printState
    move (Move (Position 2 'e') (Position 4 'e'))
    move (Move (Position 8 'b') (Position 6 'a'))
    move (Move (Position 4 'e') (Position 5 'e'))
    move (Move (Position 7 'd') (Position 5 'd'))
    move (Move (Position 5 'e') (Position 6 'd')) -- en passant
    printState
    move (Move (Position 6 'a') (Position 8 'b'))
    move (Move (Position 6 'd') (Position 7 'e'))
    move (Move (Position 8 'b') (Position 6 'a'))
    move (Move (Position 7 'e') (Position 8 'f')) -- promotion
    printState

testChess2 :: StateT BoardState (ExceptT BoardError IO) ()
testChess2 = do
    printState
    move (Move (Position 1 'g') (Position 3 'f'))
    move (Move (Position 8 'b') (Position 6 'a'))
    printState
    move (Move (Position 2 'e') (Position 3 'e'))
    printState
    move (Move (Position 7 'd') (Position 6 'd'))
    printState
    move (Move (Position 1 'f') (Position 2 'e'))
    printState
    move (Move (Position 8 'c') (Position 7 'd'))
    printState
    move' (Castle False) -- white kingside castle
    printState
    move (Move (Position 7 'e') (Position 6 'e'))
    printState
    move (Move (Position 2 'a') (Position 3 'a'))
    printState
    move (Move (Position 8 'd') (Position 7 'e'))
    printState
    move (Move (Position 3 'a') (Position 4 'a'))
    printState
    move' (Castle True)  -- black queenside castle
    printState

testChess3 :: StateT BoardState (ExceptT BoardError IO) ()
testChess3 = do
    printState
    move (Move (Position 2 'e') (Position 4 'e'))
    printState
    move (Move (Position 7 'e') (Position 5 'e'))
    printState
    move (Move (Position 1 'f') (Position 4 'c'))
    printState
    move (Move (Position 8 'b') (Position 6 'c'))
    printState
    move (Move (Position 1 'd') (Position 5 'h'))
    printState
    move (Move (Position 8 'g') (Position 6 'f'))
    printState
    move (Move (Position 5 'h') (Position 7 'f')) -- checkmate
    printState

testChess4 :: StateT BoardState (ExceptT BoardError IO) ()
testChess4 = do
    printState
    move (Move (Position 1 'g') (Position 3 'f'))
    move (Move (Position 7 'e') (Position 6 'e'))
    move (Move (Position 2 'a') (Position 3 'a'))
    move (Move (Position 8 'f') (Position 4 'b'))
    printState
    move (Move (Position 2 'd') (Position 3 'd')) -- autocheck
    printState

execTestChess :: StateT BoardState (ExceptT BoardError IO) () -> IO ()
execTestChess test = runExceptT (evalStateT test initialState) >>= \case
    Left err -> putStrLn $ "Error: " ++ show err
    Right _ -> putStrLn "Test ended"