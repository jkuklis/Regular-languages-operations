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
  
simpl :: Eq c => Reg c -> Reg c
simpl x = case x of
    Many(y) -> 
        let s = simpl(y) in case s of
            Eps -> s
            Empty -> Eps
            Many _ -> s
            _ -> Many s
        
    (l :> r) ->
        let 
            gather (l :> r) acc = gather l (gather r acc)
            gather x acc = simpl(x) : acc 
        in let g = gather x [] in 
            if (has_Empty g)
            then Empty
            else roll (remove_Eps g)
            where 
                remove_Eps :: [Reg c] -> [Reg c]
                remove_Eps g = filter (\x -> case x of Eps -> False; otherwise -> True) g
                
                has_Empty :: [Reg c] -> Bool
                has_Empty g = foldr (\x acc -> case x of Empty -> True; _ -> acc) False g
                
                roll :: [Reg c] -> Reg c
                roll [] = Eps
                roll (x:[]) = x
                roll (x:xs) = foldl' (\y acc -> y :> acc) x xs
    
    (l :| r) ->
        let 
            gather (l :| r) acc = gather l (gather r acc)
            gather x acc = simpl(x) : acc
        in let g = nub (gather x []) in 
            roll (remove_Empty g) 
            where 
                remove_Empty :: [Reg c] -> [Reg c]
                remove_Empty g = filter (\x -> case x of Empty -> False; otherwise -> True) g
                
                roll :: [Reg c] -> Reg c
                roll [] = Empty
                roll (x:[]) = x
                roll (x:xs) = foldl' (\y acc -> y :| acc) x xs
    _ -> x

nullable :: Reg c -> Bool
nullable x = case x of
    Many _ -> True
    Empty -> False
    Eps -> True
    Lit c -> False
    (x :| y) -> (nullable x) || (nullable y)
    (x :> y) -> (nullable x) && (nullable y)

empty :: Eq c => Reg c -> Bool 
empty r = (simpl r == Empty)   

der :: Eq c => c -> Reg c -> Reg c
der c r = case r of
    Lit d -> if d == c then Eps else Empty
    Eps -> Empty
    Empty -> Empty
    Many y -> simpl((der c y) :> (Many y))
    (x :| y) -> simpl((der c x) :| (der c y))
    (x :> y) -> if (nullable x)
        then simpl(((der c x) :> y) :| (der c y))
        else simpl((der c x) :> y)

ders :: Eq c => [c] -> Reg c -> Reg c
ders [] r = r
ders (x:xs) r = ders xs (der x r)

accepts :: Eq c => Reg c -> [c] -> Bool
accepts r [] = False
accepts r w = nullable (ders w r)

mayStart :: Eq c => c -> Reg c -> Bool
mayStart c r = (accepts r [c]) || not(empty (der c r)) 

match :: Eq c => Reg c -> [c] -> Maybe [c]
match r w = case (match_h r w [] Nothing) of
    Nothing -> Nothing
    Just p -> Just (reverse p)

match_h :: Eq c => Reg c -> [c] -> [c] -> Maybe [c] -> Maybe[c]
match_h r w acc prev = case w of
        [] -> prev'
        (x:xs) -> match_h (der x r) xs (x : acc) prev' 
    where prev' = if nullable r then Just acc else prev

search :: Eq c => Reg c -> [c] -> Maybe [c]
search r w = if check_eps r w 
    then Just []
    else search_h r w
            
search_h :: Eq c => Reg c -> [c] -> Maybe [c]
search_h r [] = if nullable r 
    then Just []
    else Nothing
search_h r w@(x:xs) = let m = match r w in case m of
    Nothing -> search_h r xs
    _ -> m            

check_eps :: Eq c => Reg c -> [c] -> Bool
check_eps r [] = False
check_eps r w@(x:xs) = (nullable r) && (match r w == Nothing)

findall :: Eq c => Reg c -> [c] -> [[c]]
findall r w = let rev = reverse (findall_h r w [] (-1)) in 
    if (match r w == Nothing) && (nullable r) 
        then ([] : rev)
        else rev
    
findall_h :: Eq c => Reg c -> [c] -> [[c]] -> Int -> [[c]]
findall_h r w acc lmin = case w of
    [] -> acc
    (x:xs) -> let m = match r w in case m of
        Just p -> let l = length p in
            if l >= lmin 
                then findall_h r xs (p : acc) l
                else findall_h r xs acc (lmin - 1)
        Nothing -> findall_h r xs acc (lmin - 1)

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
