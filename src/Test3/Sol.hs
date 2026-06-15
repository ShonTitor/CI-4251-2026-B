{-# LANGUAGE RecordWildCards #-}
{-# LANGUAGE TemplateHaskell #-}
{-# LANGUAGE RankNTypes #-}

module Test3.Sol where

import Control.Lens hiding (noneOf)
import Text.Parsec
import Data.Map (Map)
import Data.Map qualified as Map
import Data.Maybe
import Data.List (intercalate, isSuffixOf, sort)

-- Data Types

data Evolution = Evolution
  { _evoNum  :: String
  , _evoName :: String
  } deriving (Show, Eq)

data Pokemon = Pokemon
  { _pokeId          :: Int
  , _pokeNum         :: String
  , _pokeName        :: String
  , _pokeImg         :: String
  , _pokeType        :: [String]
  , _pokeHeight      :: String
  , _pokeWeight      :: String
  , _pokeCandy       :: String
  , _pokeCandyCount  :: Maybe Int
  , _pokeEgg         :: String
  , _pokeSpawnChance :: Double
  , _pokeAvgSpawns   :: Double
  , _pokeSpawnTime   :: String
  , _pokeMultipliers :: Maybe [Double]
  , _pokeWeaknesses  :: [String]
  , _pokeNextEvol    :: [Evolution]
  , _pokePrevEvol    :: [Evolution]
  } deriving (Show, Eq)

data PokeSet = PokeSet [Pokemon]
  deriving (Show, Eq)

{-
This datatype was chosen for simplicity. Adding a type argument was deemed unnecesary,
since we are only working with the Pokemon datatype. We could also use a map instead
of a list, but it would have little impact on performance with a dataset of 151 Pokemon.
-}

evoNum :: Lens' Evolution String
evoNum = lens _evoNum (\e x -> e { _evoNum = x })

evoName :: Lens' Evolution String
evoName = lens _evoName (\e x -> e { _evoName = x })

pokemonId :: Lens' Pokemon Int
pokemonId = lens _pokeId (\p x -> p { _pokeId = x })

num :: Lens' Pokemon String
num = lens _pokeNum (\p x -> p { _pokeNum = x })

name :: Lens' Pokemon String
name = lens _pokeName (\p x -> p { _pokeName = x })

img :: Lens' Pokemon String
img = lens _pokeImg (\p x -> p { _pokeImg = x })

pokemonType :: Lens' Pokemon [String]
pokemonType = lens _pokeType (\p x -> p { _pokeType = x })

height :: Lens' Pokemon String
height = lens _pokeHeight (\p x -> p { _pokeHeight = x })

weight :: Lens' Pokemon String
weight = lens _pokeWeight (\p x -> p { _pokeWeight = x })

candy :: Lens' Pokemon String
candy = lens _pokeCandy (\p x -> p { _pokeCandy = x })

candyCount :: Lens' Pokemon (Maybe Int)
candyCount = lens _pokeCandyCount (\p x -> p { _pokeCandyCount = x })

egg :: Lens' Pokemon String
egg = lens _pokeEgg (\p x -> p { _pokeEgg = x })

spawnChance :: Lens' Pokemon Double
spawnChance = lens _pokeSpawnChance (\p x -> p { _pokeSpawnChance = x })

avgSpawns :: Lens' Pokemon Double
avgSpawns = lens _pokeAvgSpawns (\p x -> p { _pokeAvgSpawns = x })

spawnTime :: Lens' Pokemon String
spawnTime = lens _pokeSpawnTime (\p x -> p { _pokeSpawnTime = x })

multipliers :: Lens' Pokemon (Maybe [Double])
multipliers = lens _pokeMultipliers (\p x -> p { _pokeMultipliers = x })

weaknesses :: Lens' Pokemon [String]
weaknesses = lens _pokeWeaknesses (\p x -> p { _pokeWeaknesses = x })

nextEvol :: Lens' Pokemon [Evolution]
nextEvol = lens _pokeNextEvol (\p x -> p { _pokeNextEvol = x })

prevEvol :: Lens' Pokemon [Evolution]
prevEvol = lens _pokePrevEvol (\p x -> p { _pokePrevEvol = x })

_PokeSet :: Iso' PokeSet [Pokemon]
_PokeSet = iso (\(PokeSet xs) -> xs) PokeSet

{-
I chose to use the most general optic types possible, even if unnecessary for the implementation.
_PokeSet uses Iso' since it is a bijection. The rest of the optics use Lens' because they only
need to focus on a single field.
-}

-- JSON Parser

newtype JSon = JSon (Map String JSonValue)

data JSonValue
    = JString String
    | JNum Double
    | JObject JSon
    | JArray [JSonValue]
    | JBool Bool
    | JNull

_JString :: Prism' JSonValue String
_JString = prism' JString (\case JString s -> Just s; _ -> Nothing)

_JNum :: Prism' JSonValue Double
_JNum = prism' JNum (\case JNum n -> Just n; _ -> Nothing)

_JObject :: Prism' JSonValue JSon
_JObject = prism' JObject (\case JObject o -> Just o; _ -> Nothing)

_JArray :: Prism' JSonValue [JSonValue]
_JArray = prism' JArray (\case JArray a -> Just a; _ -> Nothing)

_JBool :: Prism' JSonValue Bool
_JBool = prism' JBool (\case JBool b -> Just b; _ -> Nothing)

_JNull :: Prism' JSonValue ()
_JNull = prism' (const JNull) (\case JNull -> Just (); _ -> Nothing)

{-
For these optics I used Prism because they fit naturally for our purposes of extracting values
from the JSonValue type implemented in class as a sum type.
Lens could also be used by returning Maybes, but using Prism allows us to compose optics more 
easily and work with sum types in a more declarative way.
-}

instance Show JSonValue where
    show (JString s) = show s
    show (JNum n) = show n
    show (JObject o) = show o
    show (JArray a) = "[" ++ intercalate ", " (map show a) ++ "]"
    show (JBool b) = if b then "true" else "false"
    show JNull = "null"

instance Show JSon where
    show (JSon m) = "{" ++ intercalate ", " (map showPair (Map.toList m)) ++ "}"
        where
        showPair (k, v) = show k ++ ": " ++ show v

parseJSon :: Parsec String () JSon
parseJSon = between (char '{') (char '}')
    $ (pure f <* spaces')
    <*> ( (
            (,)
            <$> (pString <* spaces' <* char ':' <* spaces')
            <*> parseJSonValue
          ) `sepBy` (spaces' *> char ',' *> spaces'))
    where
    f :: [(String, JSonValue)] -> JSon
    f = JSon . Map.fromList

parseJSonValue :: Parsec String () JSonValue
parseJSonValue = pWhiteSpace *>
        ( pStringValue
        <|> pNumberValue
        <|> pObjectValue
        <|> pArrayValue
        <|> pBoolValue
        <|> pNullValue
        ) <* pWhiteSpace where
    pStringValue = JString <$> pString
    pNumberValue = JNum <$> pNumber
    pObjectValue = JObject <$> parseJSon
    pArrayValue  = JArray <$> between (char '[') (char ']') (parseJSonValue `sepBy` (spaces' *> char ',' *> spaces'))
    pBoolValue   = JBool <$> ((True <$ string "true") <|> (False <$ string "false"))
    pNullValue   = pNull

pWhiteSpace :: Parsec String () ()
--pWhiteSpace = (space <|> newline <|> crlf <|> tab) *> optional pWhiteSpace
pWhiteSpace = skipMany $ space <|> newline <|> crlf <|> tab

spaces' :: Parsec String () ()
spaces' = pWhiteSpace
pNumber :: Parsec String () Double
pNumber = f
    <$> optionMaybe (char '-')
    <*> many1 digit
    <*> optionMaybe (char '.' *> many1 digit)
    <*> optionMaybe
        ( (char 'e' <|> char 'E')
        *> pure (,)
        <*> optionMaybe (char '+' <|> char '-')
        <*> many1 digit
    )
    where
    f :: Maybe Char -> [Char] -> Maybe [Char] -> Maybe (Maybe Char, [Char]) -> Double
    f mSign intPart mFrac mExp =
        let sign = fromMaybe ' ' mSign
            frac = maybe "" ('.' :) mFrac
            exp  = case mExp of
                Nothing -> ""
                Just (mSign', expPart) -> "e" <> (fromMaybe ' ' mSign' : expPart)
        in read $ (sign : intPart) <> frac  <> exp

pString :: Parsec String () String
pString = between (char '"') (char '"') $ pString' where
    pString' :: Parsec String () String
    pString' = fmap concat . many $ ((:[]) <$> noneOf ['"','\\']) <|>
        (f
        <$> char '\\'
        <*> ( (pure <$> (choice . fmap char) ['"', '\\', '/', 'b', 'f', 'n', 'r', 't'])
            <|> ( (:) <$> char 'u' <*> count 4 hexDigit )
            )
        )
    f :: Char -> String -> String
    f = (:)

pNull :: Parsec String () JSonValue
pNull = JNull <$ string "null"

pPokeSet :: Parsec String () PokeSet
pPokeSet = jsonToPokeSet <$> parseJSon

-- Helpers

jsonToPokeSet :: JSon -> PokeSet
jsonToPokeSet (JSon m) = PokeSet $ mapMaybe jsonToPokemon $
    fromMaybe [] $ m ^? ix "pokemon" . _JArray

jsonToPokemon :: JSonValue -> Maybe Pokemon
jsonToPokemon (JObject (JSon m)) = do
    _pokeId          <- m ^? ix "id"           . _JNum    . to truncate
    _pokeNum         <- m ^? ix "num"          . _JString
    _pokeName        <- m ^? ix "name"         . _JString
    _pokeImg         <- m ^? ix "img"          . _JString
    _pokeType        <- m ^? ix "type"         . _JArray  . to (^.. each . _JString)
    _pokeHeight      <- m ^? ix "height"       . _JString
    _pokeWeight      <- m ^? ix "weight"       . _JString
    _pokeCandy       <- m ^? ix "candy"        . _JString
    _pokeCandyCount  <- pure $ m ^?  ix "candy_count"  . _JNum . to truncate
    _pokeEgg         <- m ^? ix "egg"          . _JString
    _pokeSpawnChance <- m ^? ix "spawn_chance" . _JNum
    _pokeAvgSpawns   <- m ^? ix "avg_spawns"   . _JNum
    _pokeSpawnTime   <- m ^? ix "spawn_time"   . _JString
    _pokeMultipliers <- pure $ m ^?  ix "multipliers"  . _JArray . to (^.. each . _JNum)
    _pokeWeaknesses  <- m ^? ix "weaknesses"   . _JArray  . to (^.. each . _JString)
    _pokeNextEvol    <- pure $ m ^.. ix "next_evolution" . _JArray . each . _JObject . to jsonToEvolution
    _pokePrevEvol    <- pure $ m ^.. ix "prev_evolution" . _JArray . each . _JObject . to jsonToEvolution
    return Pokemon{..}
jsonToPokemon _ = Nothing

jsonToEvolution :: JSon -> Evolution
jsonToEvolution (JSon m) = Evolution
    { _evoNum  = fromMaybe "" (m ^? ix "num" . _JString)
    , _evoName = fromMaybe "" (m ^? ix "name" . _JString)
    }

avgOf :: Fold s Double -> s -> Double
avgOf f s = sumOf f s / fromIntegral (lengthOf f s)

varOf :: Fold s Double -> s -> Double
varOf f s = avgOf (f . to (^2)) s - avgOf f s ^ 2

corrOf :: Fold s (Double, Double) -> s -> Double
corrOf f s = (avgOf (f . to (uncurry (*))) s - avgOf (f . to fst) s * avgOf (f . to snd) s)
           / sqrt (varOf (f . to fst) s * varOf (f . to snd) s)

quantile :: [Double] -> Double -> Double
quantile xs p = xs !! (floor (p * fromIntegral (length xs - 1)) :: Int)

iqrOf :: Fold s Double -> s -> (Double, Double, Double, Double)
iqrOf f = (\xs -> (quantile xs 0.25, quantile xs 0.5, quantile xs 0.75, quantile xs 0.75 - quantile xs 0.25))
        . sort . toListOf f

spawnTimeToDouble :: String -> Double
spawnTimeToDouble = (\(h, m) -> fromIntegral (read h * 60 + read (tail m) :: Int)) . span (/= ':')

parseWeight :: String -> Double
parseWeight = read . head . words

-- Queries
{-
Optic decision reasoning:

each (Traversal'): I chose it so that it could be used along with %~. 
This wouldn't have been possible with a Fold, as Folds don't admit setters.

filtered (Fold): I chose it because it was the easiest for me to wrap my head around.
I couldn't think of a different implementation.

to f (Getter): It allows me to lift a pure function into the optic context.
Since an arbitrary pure function is not invertible, it couldn't have been a Lens.

In general I chose what felt more natural and readable for me, but I might be missing something.
-}

-- Returns a list with the names of each pokemon in the dataset.
pokeNames :: PokeSet -> [String]
pokeNames ps = ps ^.. _PokeSet . each . name

-- Returns a list with the names of each pokemon and its next evolutions
-- That is: ("Bulbasaur", ["Ivysaur", "Venusaur"]) and ("IviSaur", ["Venusaur"])
-- are both in the list
pokeEvolutions :: PokeSet -> [(String, [String])]
pokeEvolutions ps = ps ^.. _PokeSet . each . to (\p -> (p ^. name, p ^.. nextEvol . each . evoName))

-- Same as pokeEvolutions, but it should return only the base pokemons
-- (that is, the pokemons that are not evolutions of any other pokemon).
-- Do NOT use or mention `pokeEvolutions` in your implementation.
pokeEvolutions' :: PokeSet -> [(String, [String])]
pokeEvolutions' ps = ps ^.. _PokeSet . each . filtered (null . view prevEvol) 
                    . to (\p -> (p ^. name, p ^.. nextEvol . each . evoName))

-- Filters all the pokemons that are of type "Psychic" and "Normal"
-- increasing their multipliers by 2.
pokePsychicNormal :: PokeSet -> PokeSet
pokePsychicNormal ps = PokeSet $ ps ^.. _PokeSet . each
                       . filtered (\p -> "Psychic" `elem` (p ^. pokemonType) && "Normal" `elem` (p ^. pokemonType))
                       . to (\p -> p & multipliers . _Just . each +~ 2)

-- Filters all the pokemons that are of type "Psychic" or "Normal"
-- decreasing their multipliers by 1.
pokePsychicNormal' :: PokeSet -> PokeSet
pokePsychicNormal' ps = PokeSet $ ps ^.. _PokeSet . each
                       . filtered (any (\t -> elem t ["Psychic", "Normal"]) . view pokemonType)
                       . to (\p -> p & multipliers . _Just . each -~ 1)

-- set the image of the pokemons `x` that have an an evolution `y`,
-- such that their evolution `y` weights more than them to the image of `y`.
pokeDrinker :: PokeSet -> PokeSet
pokeDrinker ps = ps & _PokeSet . each %~ \x ->
    x & img .~ maybe (x ^. img) (^. img)
        (listToMaybe $ ps ^.. _PokeSet . each
            . filtered (\y -> y ^. name `elem` (x ^.. nextEvol . each . evoName)
                           && parseWeight (y ^. weight) > parseWeight (x ^. weight)))

-- Return the name(s) of the pokemon(s) with the most amount of weaknesses.
pokeWeakest :: PokeSet -> [String]
pokeWeakest ps = ps ^.. _PokeSet . each
    . filtered (\p -> length (p ^. weaknesses) ==
                      maximum (ps ^.. _PokeSet . each . weaknesses . to length))
    . name

-- Returns the average weight of all the pokemons in the dataset.
pokeAvgWeight :: PokeSet -> Double
pokeAvgWeight ps = avgOf ( _PokeSet . each . to (\p -> read (head (words (p ^. weight))) :: Double)) ps

-- Returns the variance of the weight of all the pokemons in the dataset.
pokeVarWeight :: PokeSet -> Double
pokeVarWeight ps = varOf ( _PokeSet . each . to (\p -> read (head (words (p ^. weight))) :: Double)) ps

-- Returns the pearson correlation coefficient between the weight and height of all the pokemons in the dataset.
pokeCorr :: PokeSet -> Double
pokeCorr = corrOf (_PokeSet . each
                   . to (\p -> ( read (head (words (p ^. weight))) :: Double
                               , read (head (words (p ^. height))) :: Double)))

-- Modifies every `"name": pokeName` field in the dataset to `"name": pokeName tuff`,
-- where `pokeName` is the original name of the pokemon, and `pokeName tuff` is the original name concatenated with the string " tuff".
-- If the name already ends with "tuff", it should not be modified.
-- Remember that name can appear in multiple places in a single record.
pokeTuff :: PokeSet -> PokeSet
pokeTuff ps = ps & _PokeSet . each . name
                 %~ (\n -> if "tuff" `isSuffixOf` n then n else n ++ " tuff")
                 & _PokeSet . each . nextEvol . each . evoName
                 %~ (\n -> if "tuff" `isSuffixOf` n then n else n ++ " tuff")
                 & _PokeSet . each . prevEvol . each . evoName
                 %~ (\n -> if "tuff" `isSuffixOf` n then n else n ++ " tuff")

{-
  .-----------------------------.
  | AMC 99                      |
  |            .~~-.      _.    |
  |  .''..    (_~)  ) _.-'. ;   |
  |  '.'..'..-(_~ _-'*. .'.'    |
  |    ''.'.. _ ~~  _  ';'      |
  |     .''. (_)   (_)  '.      |
  |     ;      "..."     '.     |
  | .''.'.   .''`-'''.    '.''. |
  | '.  '   ;         ;    ;  ; |
  |   '.   ;           ;   ' ;  |
  |    '.  ;           ;    ;   |
  |     '.  ;         ;   .'    |
  |     .'...:..___..:..':.     |
  |  .''     ..'    '...   ~)   |
  | (.....'''           ''''    |
  |    ,                        |
  | PokeMon # 040 - Wigglytuff  |
  `-----------------------------'
  source: https://ascii.co.uk/art/pokemon
-}

-- Returns the Quantile 1,2,3 and the Interquantile range of the SPAWN TIME of all the pokemons in the
-- dataset.
pokeIQR :: PokeSet -> (Double,Double,Double,Double)
pokeIQR = iqrOf (_PokeSet . each . spawnTime . filtered (/= "N/A") . to spawnTimeToDouble)

-- Use the pokeIQR to build a visual representation of the box plot.
pokeBoxPlot :: PokeSet -> String
pokeBoxPlot ps =
    (\(q1, q2, q3, _) ->
        (\mn mx ->
            (\sc ->
                "|" ++ replicate (sc q1 - 1)        '-'
                    ++ "|" ++ replicate (sc q2 - sc q1 - 1) '-'
                    ++ "|" ++ replicate (sc q3 - sc q2 - 1) '-'
                    ++ "|" ++ replicate (100 - sc q3 - 1)    '-'
                    ++ "|\n"
                    ++ "min=" ++ show (round mn :: Int)
                    ++ " Q1=" ++ show (round q1 :: Int)
                    ++ " Q2=" ++ show (round q2 :: Int)
                    ++ " Q3=" ++ show (round q3 :: Int)
                    ++ " max=" ++ show (round mx :: Int)
                    ++ " (minutes after midnight)"
            )
            (\v -> round ((v - mn) / (mx - mn) * 100) :: Int)
        )
        (minimum (ps ^.. _PokeSet . each . spawnTime . filtered (/= "N/A") . to spawnTimeToDouble))
        (maximum (ps ^.. _PokeSet . each . spawnTime . filtered (/= "N/A") . to spawnTimeToDouble))
    )
    (pokeIQR ps)

-- Returns a contingency table of the types (rows)/weaknesses (cols) of the pokemons in the dataset.
-- The representation of the contingency table is up to you, but it MUST be indexable
-- using a tuple: `pokeContingency ^? ix ("water","fire")`
pokeContingency :: PokeSet -> Map (String, String) Int
pokeContingency ps = Map.fromListWith (+) $
    ps ^.. _PokeSet . each
           . to (\p -> [(t, w) | t <- p ^. pokemonType, w <- p ^. weaknesses])
           . each
           . to (, 1)

data Histo = Histo
  { _histoTitle   :: String
  , _histoBuckets :: [(String, Int)]
  }

instance Show Histo where
    show (Histo title buckets) = unlines $
        title : map (\(label, n) -> replicate n '■' ++ " (" ++ show n ++ ") " ++ label) buckets

-- Build an histogram for the egg distance. It's up to you to decide the
-- intervals.
-- The histogram should have a `Show` instance that pretty prints it.
-- The `Show` instance should not hold any logic, it should only pretty print.
pokeHist :: PokeSet -> Histo
pokeHist ps = Histo
    { _histoTitle   = "Egg Distance"
    , _histoBuckets = Map.toList $ Map.fromListWith (+) $
        ps ^.. _PokeSet . each . egg . to (, 1)
    }

-- 
test :: IO ()
test = do
  contents <- readFile "src/Test3/pokedex.json"
  case parse pPokeSet "" contents of
    Left err     -> putStrLn $ show err
    Right pokeSet -> do
      --putStrLn $ show $ pokeHist pokeSet
      print $ pokeDrinker pokeSet ^.. _PokeSet . each . to (\p -> (p ^. name, p ^. img))
