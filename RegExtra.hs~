module RegExtra where
import Mon
import Reg
import Data.List

data AB = A | B deriving(Eq,Ord,Show)

infix 4 ===
class Equiv a where
  (===) :: a -> a -> Bool

instance (Eq c) => Equiv (Reg c) where
   r1 === r2 = (simpl r1) == (simpl r2)

instance Mon (Reg c) where
  m1 = Eps
  x <> y = x :> y
  
simpl :: Reg c -> Reg c
simpl x = case x of
    Many(y) -> let s = simpl(y) in case s of
        Eps -> s
        Empty -> s
        Many(_) -> s
        _ -> Many(s)
    (l :> r) -> let ls = simpl(l) in case ls of
        Eps -> simpl(r)
        Empty -> Empty
        _ -> let rs = simpl(r) in case rs of
            Eps -> ls
            Empty -> Empty
            _ -> (ls :> rs)
    (l :| r) -> let ls = simpl(l) in let rs = simpl(r) in case ls of
        Empty -> rs
        _ -> case rs of
            Empty -> ls
            _ -> (ls :| rs)   
    _ -> x

gather_c :: Reg c -> [Reg c]
gather_c x = case x of
    (l :> r) -> (gather_c l) ++ (gather_c r)
    _ -> [simpl(x)]
    
has a [] = False
has a (x:xs)
    | a == x = True
    | otherwise = has a xs    



nullable :: Reg c -> Bool
nullable x = case x of
    Many(_) -> True
    Empty -> False
    Eps -> True
    Lit c -> False
    (x :| y) -> (nullable x) || (nullable y)
    (x :> y) -> (nullable x) && (nullable y)

empty :: Reg c -> Bool 
empty r = case simpl(r) of
    Empty -> True
    _ -> False    

der :: c -> Reg c -> Reg c
der c r = case r of
    Lit c -> Eps
    Eps -> Eps
    Empty -> Empty
    Many(y) -> simpl((der c y) :> Many(y))
    (x :| y) -> simpl((der c x) :| (der c y))
    (x :> y) -> if (nullable x) 
        then simpl(((der c x) :> y) :| (der c y))
        else simpl((der c x) :> y)

ders :: Eq c => [c] -> Reg c -> Reg c
ders c r = case c of
    [] -> r
    (x:xs) -> ders xs (der x r)

accepts :: Eq c => Reg c -> [c] -> Bool
accepts r w = if nullable (ders w r)
    then True
    else False

mayStart :: Eq c => c -> Reg c -> Bool
mayStart c r = (accepts r [c]) || not(empty (der c r)) 

match :: Eq c => Reg c -> [c] -> Maybe [c]
match r w = case (match_h r w Nothing) of
    Nothing -> Nothing
    Just p -> Just (reverse p)

match_h :: Eq c => Reg c -> [c] -> Maybe [c] -> Maybe [c]
match_h r w acc = case w of
    [] -> acc
    (x:xs) -> let d = der x r in case d of
        Empty -> if (accepts d [x])
            then case acc of
                Nothing -> Just [x]
                Just p -> Just (x : p)
            else acc
        _ -> case acc of
            Nothing -> match_h d xs (Just [x])
            Just p -> match_h d xs (Just (x : p))

search :: Eq c => Reg c -> [c] -> Maybe [c]
search r w = case w of
    [] -> Nothing
    (x:xs) -> if (mayStart x r)
        then match r w
        else search r xs

findall :: Eq c => Reg c -> [c] -> [[c]]
findall r w = findall_h r w []

findall_h :: Eq c => Reg c -> [c] -> [[c]] -> [[c]]
findall_h r w acc = case w of
    [] -> acc
    (x:xs) -> if (mayStart x r)
        then let Just p = match r w in findall_h r xs (p : acc)
        else findall_h r xs acc

char :: Char -> Reg Char
char = Lit

string :: [Char] -> Reg Char
string = foldr1 (:>) . map Lit

alts :: [Char] -> Reg Char
alts = foldr1 (:|) . map Lit

letter = alts ['a'..'z'] :| alts ['A'..'Z']
digit = alts ['0'..'9']
number = digit :> Many digit
ident = letter :> Many (letter :| digit)

many1 r = r :> Many r
