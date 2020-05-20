------------------------------------------------------------------------
-- 
-- Module: PromelaParser.Basic
-- Author: Dennis Kraft
--
-- basic parsers and combinators
-- 
------------------------------------------------------------------------


module Basic where


import Prelude


-- parser datatype -----------------------------------------------------


newtype Parser a = Parser ([Char] -> Consumed a)


data Consumed a = Consumed (Result a)
   | Empty (Result a)
   deriving (Show, Eq)


data Result a = Ok a [Char] Pos [Message] 
   | Fail [Char] Pos [Message]
   deriving (Show, Eq)


type Pos = (Integer, Integer)
type Message = String


instance Monad Parser where
   return a = basicReturn a
   p >>= f = basicBind p f
   fail s = basicFail s


parser :: Parser a -> ([Char] -> Consumed a)
parser (Parser p) = p


-- position functions --------------------------------------------------


initPos :: Maybe Char -> Pos
initPos Nothing = (1, 0)
initPos (Just '\n') = (2, 0)
initPos (Just _) = (1, 1)


addPos :: Pos -> Pos -> Pos
addPos (x1, y1) (1, y2) = (x1, y1 + y2)
addPos (x1, y1) (x2, y2) = (x1 + x2 - 1, y2)


-- basic parsers and combinators ---------------------------------------


basicReturn :: a -> Parser a
basicReturn a = Parser (\cs -> Empty (Ok a cs (initPos Nothing) []))


basicFail :: Message -> Parser a
basicFail msg = Parser (\cs -> Empty (Fail cs (initPos Nothing) [msg]))


satisfy :: (Char -> Bool) -> Parser Char
satisfy f = Parser (\cs -> case cs of
   [] -> Empty (Fail [] (initPos Nothing) [])
   (c : cs') | f c -> Consumed (Ok c cs' (initPos (Just c)) [])
             | otherwise -> Empty (Fail cs (initPos Nothing) []))

-- TODO: change this such that position counter works for jump!!!
basicBind :: Parser a -> (a -> Parser b) -> Parser b
basicBind p f = Parser (\cs -> case parser p cs of
   Empty res1 -> case res1 of
      Ok a cs' _ _ -> parser (f a) cs'
      Fail cs' pos1 msgs -> Empty (Fail cs' pos1 msgs)
   Consumed res1 -> Consumed (case res1 of
      Ok a cs' pos1 _ -> case parser (f a) cs' of
         Consumed res2 -> case res2 of
            Ok b cs'' pos2 msgs -> Ok b cs'' (addPos pos1 pos2) msgs
            Fail cs'' pos2 msgs -> Fail cs'' (addPos pos1 pos2) msgs
         Empty reply2 -> case reply2 of
            Ok b cs'' pos2 msgs -> Ok b cs'' (addPos pos1 pos2) msgs
            Fail cs'' pos2 msgs -> Fail cs'' (addPos pos1 pos2) msgs
      Fail cs' pos1 msgs -> Fail cs' pos1 msgs))


(<|>) :: Parser a -> Parser a -> Parser a
p <|> q = Parser (\cs -> case parser p cs of
   Empty (Fail cs' pos msgs1)  -> case parser q cs of
      Empty (Fail _ _ msgs2) -> Empty (Fail cs' pos (msgs1 ++ msgs2))
      other -> other   
   Empty ok -> case parser q cs of
      Empty _ -> Empty ok
      consumed -> consumed
   consumed -> consumed)


(<||>) :: Parser a -> Parser a -> Parser a
p <||> q = Parser (\cs -> case parser p cs of
   Empty (Fail cs' pos msgs1)  -> case parser q cs of
      Empty (Fail _ _ msgs2) -> Empty (Fail cs' pos (msgs2))
      other -> other   
   Empty ok -> case parser q cs of
      Empty _ -> Empty ok
      consumed -> consumed
   consumed -> consumed)


try :: Parser a -> Parser a
try p = Parser (\cs -> case parser p cs of
   Consumed (Fail cs' pos msgs) -> Empty (Fail cs (initPos Nothing) msgs)
   other -> other)


jump :: Parser a -> Parser a
jump p = Parser (\cs -> case parser p cs of
   Consumed x -> Empty x
   other -> other)


-- useful parsers ------------------------------------------------------


one :: Parser Char
one = satisfy (\_ -> True)


item :: Char -> Parser Char
item c = satisfy (==c)


items :: [Char] -> Parser [Char]
items [] = return []
items (c : cs) = try (do
   c' <- item c
   cs' <- items cs
   return (c' : cs'))


convert :: (a -> b) -> Parser a -> Parser b
convert f p = do
   a <- p
   return (f a)


list :: Parser a -> Parser [a]
list p = listOne p <|> return []


listOne :: Parser a -> Parser [a]
listOne p = do 
   a <- p
   as <- (listOne p <|> return [])
   return (a : as)


listAll :: Parser a -> Parser [a]
listAll p = do 
      a <- p
      as <- (listAll p <|> end)
      return (a : as)
   where end = Parser (\cs -> case cs of
            [] -> Empty (Ok [] [] (initPos Nothing) [])
            cs' -> Empty (Fail cs' (initPos Nothing) []))
         

enclose :: Parser a -> Parser b -> Parser c -> Parser c
enclose l r p = do
   a <- l
   c <- p
   b <- r
   return (c)


perhaps :: Parser a -> Parser (Maybe a)
perhaps p = convert Just p <|> return Nothing

