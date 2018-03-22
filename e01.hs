mul x y = x * y

square x = mul x x

area r = pi * square r

pyth n = [(x, y, z, y/x) | x<-[1..n], y<-[1..n], z<-[1..n], x*x+y*y==z*z, x < y]

has a [] = False
has a (x:xs)
    | a == x = True
    | otherwise = has a xs

get_ratio l (x,y,z,r)
    | has r l = l
    | otherwise = r : l

ratios l = map (get_ratio []) l

chunk n xs = chunk' 3 xs
    where
        chunk' _ [] = []
        chunk' n xs = a : chunk' n b where (a,b) = splitAt n xs
        
has2 _ [] = False
has2 a y@(x:xs)
    | a == x = True
    | otherwise = has a xs
