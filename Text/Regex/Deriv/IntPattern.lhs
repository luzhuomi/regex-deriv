> {-# LANGUAGE BangPatterns #-}
> -- | This module defines the data type of internal regular expression pattern, 
> -- | as well as the partial derivative operations for regular expression patterns.
> module Text.Regex.Deriv.IntPattern 
>     ( Pat(..)
>     , strip
>     , Binder
>     , toBinder
>     , listifyBinder
>     , Key(..)
>     )
>     where

> import Data.List
> import qualified Data.IntMap as IM
> import Text.Regex.Deriv.Common (Range(..), range, minRange, maxRange, Letter, PosEps(..), IsEps(..), IsPhi(..), GFlag(..), IsGreedy(..), Simplifiable(..) )
> import Text.Regex.Deriv.RE
> import Text.Regex.Deriv.Dictionary (Key(..), primeL, primeR)
> import Text.Regex.Deriv.Pretty


> -- | regular expression patterns
> data Pat = PVar Int [Range] Pat       -- ^ variable pattern 
>   | PE [RE]                           -- ^ pattern without binder
>   | PPair Pat Pat                     -- ^ pair pattern
>   | PChoice [Pat] GFlag             -- ^ choice pattern 
>   | PStar Pat GFlag                   -- ^ star pattern 
>   | PPlus Pat Pat                     -- ^ plus pattern, it is used internally to indicate that it is unrolled from a PStar
>   | PEmpty Pat                        -- ^ empty pattern, it is used intermally to indicate that mkEmpty function has been applied.
>   deriving Show      

> {-| The Eq instance for Pat data type
>     NOTE: We ignore the 'consumed word' when comparing patterns
>     (ie we only compare the pattern structure).
>     Essential for later comparisons among patterns. -}

> instance Eq Pat where
>   (==) (PVar x1 _ p1) (PVar x2 _ p2) = (x1 == x2) && (p1 == p2) 
>   (==) (PPair p1 p2) (PPair p1' p2') = (p1 == p1') && (p2 == p2')
>   (==) (PChoice ps1 g1) (PChoice ps2 g2) = (g1 == g2) && (ps1 == ps2) -- more efficient, because choices are constructed in left-nested
>   (==) (PPlus p1 p2) (PPlus p1' p2') = (p1 == p1') && (p2 == p2')
>   (==) (PStar p1 g1) (PStar p2 g2) =  (g1 == g2) && (p1 == p2)
>   (==) (PE rs1) (PE rs2) = rs1 == rs2
>   (==) _ _ = False
> 

> instance Pretty a => Pretty [a] where
>     pretty [] = "{}"
>     pretty a@(x:xs) = "{" ++ prettyAll ++ "}"
>        where prettyAll = foldl' (\a i -> a++","++(pretty i)) (pretty x) xs

> instance Pretty Pat where
>     pretty (PVar x1 _ p1) = "(" ++ show x1 ++ ":" ++ pretty p1 ++ ")"
>     pretty (PPair p1 p2) = "<" ++ pretty p1 ++ "," ++ pretty p2 ++ ">"
>     pretty (PChoice ps g) = "(" ++ pretty ps ++ ")" ++ (show g)
>     pretty (PE rs) = "|" ++ show rs ++ "|"
>     pretty (PPlus p1 p2 ) = "(" ++ pretty p1 ++ "," ++ pretty p2 ++ ")"
>     pretty (PStar p g) = (pretty p) ++ "*" ++ (show g)
>     pretty (PEmpty p) = "[" ++ pretty p ++ "]"

> {-
> instance Show Pat where
>     show pat = pretty pat
> -}


> instance Key Pat where
>     hash (PVar x1 _ p1) = let y1 = head (hash x1) 
>                               y2 = head (hash p1)
>                           in y1 `seq` y2 `seq` [ 1 + y1 * primeL + y2 * primeR ] 
>     hash (PPair p1 p2) = let x1 = head (hash p1)
>                              x2 = head (hash p2)
>                          in x1 `seq` x2 `seq` [ 2 + x1 * primeL + x2 * primeR ] 
>     hash (PChoice (p1:p2:_) Greedy) = let x1 = head (hash p1)
>                                           x2 = head (hash p2)
>                                       in x1 `seq` x2 `seq`  [ 4 + x1 * primeL + x2 * primeR ] 
>     hash (PChoice (p1:p2:_) NotGreedy) = let x1 = head (hash p1)
>                                              x2 = head (hash p2)
>                                          in x1 `seq` x2 `seq` [ 5 + x1 * primeL + x2 * primeR ]
>     hash (PChoice (p1:_) _) = let x1 = head (hash p1)
>                           
>                               in x1 `seq`  [ 5 + x1 * primeL ]
>     hash (PChoice [] _) = [5]
>     hash (PPlus p1 p2) = let x1 = head (hash p1)
>                              x2 = head (hash p2)
>                          in x1 `seq` x2 `seq` [ 6 + x1 * primeL + x2 * primeR ]
>     hash (PStar p Greedy) = let x = head (hash p)
>                             in x `seq` [ 7 + x * primeL ]
>     hash (PStar p NotGreedy) = let x = head (hash p)
>                             in x `seq` [ 8 + x * primeL ]
>     hash (PE r) = let x = head (hash r)
>                   in x `seq` [ 9 + x * primeL ]
>     hash (PEmpty p) = let x = head (hash p)
>                       in x `seq` [ 3 + x * primeL ]
>     hash p = error ("hash is applied to an unacceptable pattern " ++ (show p))

> -- | function 'strip' strips away the bindings from a pattern
> strip :: Pat -> RE 
> strip (PVar _ w p) = strip p
> strip (PE rs) = resToRE rs
> strip (PStar p g) = Star (strip p) g
> strip (PPair p1 p2) = Seq (strip p1) (strip p2)
> strip (PPlus p1 p2) = Seq (strip p1) (strip p2)
> strip (PChoice ps g) = Choice (map strip ps) g
> strip (PEmpty p) = strip p


> -- | function 'mkEmpPat' makes an empty pattern
> mkEmpPat :: Pat -> Pat
> mkEmpPat (PVar x w p) = PVar x w (mkEmpPat p)
> mkEmpPat (PE rs) 
>   | any posEps rs = PE [Eps]
>   | otherwise = PE [Phi]
> mkEmpPat (PStar p g) = PE [Eps] -- problematic?! we are losing binding (x,()) from  ( x : a*) ~> PE <>
> mkEmpPat (PPlus p1 p2) = mkEmpPat p1 -- since p2 must be pstar we drop it. If we mkEmpPat p2, we need to deal with pdPat (PPlus (x :<>) (PE <>)) l
> mkEmpPat (PPair p1 p2) = PPair (mkEmpPat p1) (mkEmpPat p2)
> mkEmpPat (PChoice ps g) = PChoice (map mkEmpPat ps) g

> -- | function 'getBindingsFrom' transfer bindings from p2 to p1
> getBindingsFrom :: Pat  -- ^ the source of the  
>                    -> Pat -> Pat
> getBindingsFrom p1 p2 = let b = toBinder p2
>                         in assign p1 b
>     where assign :: Pat -> Binder -> Pat
>           assign (PVar x w p) b = 
>               case IM.lookup x b of
>                  Nothing -> let p' = assign p b in PVar x w p'
>                  Just rs -> let
>                                 p' = assign p b 
>                             in PVar x (w ++ rs) p'
>           assign (PE r) _ = PE r
>           assign (PPlus p1 p2) b = PPlus (assign p1 b) p2 -- we don't need to care about p2 since it is a p*
>           assign (PPair p1 p2) b = PPair (assign p1 b) (assign p2 b)
>           assign (PChoice ps g) b = PChoice (map (\p -> assign p b) ps) g



> -- | Function 'isGreedy' checks whether a pattern is greedy
> instance IsGreedy Pat where
>     isGreedy (PVar _ _ p) = isGreedy p
>     isGreedy (PE rs) = any isGreedy rs
>     isGreedy (PPair p1 p2) = isGreedy p1 || isGreedy p2
>     isGreedy (PChoice ps Greedy) = True
>     isGreedy (PChoice ps NotGreedy) = False -- isGreedy p1 || isGreedy p2
>     isGreedy (PEmpty p) = False
>     isGreedy (PStar p Greedy) = True
>     isGreedy (PStar p NotGreedy) = False
>     isGreedy (PPlus p p') = isGreedy p || isGreedy p'


> -- | The 'Binder' type denotes a set of (pattern var * range) pairs
> -- type Binder = [(Int, [Range])]
> type Binder = IM.IntMap [Range]


> -- | check whether a pattern has binder
> hasBinder :: Pat -> Bool
> hasBinder (PVar _ _ _) = True                              
> hasBinder  (PPair p1 p2) = (hasBinder p1) || (hasBinder p2)
> hasBinder  (PPlus p1 p2) = hasBinder p1 
> hasBinder  (PStar p1 g)  = hasBinder p1 
> hasBinder  (PE rs)        = False
> hasBinder  (PChoice ps g) = any hasBinder ps 
> hasBinder  (PEmpty p) = hasBinder p
                                                      

> -- | Function 'toBinder' turns a pattern into a binder
> toBinder :: Pat -> Binder
> toBinder p = IM.fromList (toBinderList p)

> toBinderList :: Pat -> [(Int, [Range])]
> toBinderList  (PVar i rs p) = [(i, rs)] ++ (toBinderList p)
> toBinderList  (PPair p1 p2) = (toBinderList p1) ++ (toBinderList p2)
> toBinderList  (PPlus p1 p2) = (toBinderList p1) 
> toBinderList  (PStar p1 g)    = (toBinderList p1) 
> toBinderList  (PE rs)        = []
> toBinderList  (PChoice ps g) = concatMap toBinderList ps 
> toBinderList  (PEmpty p) = toBinderList p

> listifyBinder :: Binder -> [(Int, [Range])]
> listifyBinder b = sortBy (\ x y -> compare (fst x) (fst y)) (IM.toList b)
>                   

> {-| Function 'updateBinderByIndex' updates a binder given an index to a pattern var
>     ASSUMPTION: the var index in the pattern is linear. e.g. no ( 0 :: R1, (1 :: R2, 2 :a: R3))
> -}

> updateBinderByIndex :: Int 
>                     -> Int 
>                     -> Binder 
>                     -> Binder
> updateBinderByIndex i !pos binder =  -- binder  {-
>     IM.update (\ r -> case r of  -- we always initialize to [], we don't need to handle the key miss case
>                       {  (rs_@((Range b e):rs)) -> 
>                           let !e' =  e + 1
>                           in case e' of                                                    
>                              _ | pos == e' -> Just ((range b e'):rs)
>                                | pos > e'  -> Just ((range pos pos):rs_)
>                                | otherwise    -> error "impossible, the current letter position is smaller than the last recorded letter"   
>                       ; [] -> Just [(range pos pos)] 
>                       } ) i binder -- -}
> {-
> updateBinderByIndex i pos binder = 
>     case IM.lookup i binder of
>       { Nothing -> IM.insert i [(pos, pos)] binder
>       ; Just ranges -> 
>         case ranges of 
>         { [] -> IM.update (\_ -> Just [(pos,pos)]) i binder
>          ; ((b,e):rs)
>           | pos == e + 1  -> IM.update (\_ -> Just ((b,e+1):rs)) i binder 
>           | pos > e + 1 -> IM.update (\_ -> Just ((pos,pos):(b,e):rs)) i binder
>           | otherwise     -> error "impossible, the current letter position is smaller than the last recorded letter"   
>         }
>       }
> -}
> {-
> {-# INLINE updateBinderByIndex #-}
> updateBinderByIndex :: Int    -- ^ the indext of the pattern variable
>                        -> Int -- ^ the letter position
>                        -> Binder -> Binder
> updateBinderByIndex i lpos binder =
>     updateBinderByIndexSub i lpos binder 
> 
> {-# INLINE updateBinderByIndexSub #-}
> updateBinderByIndexSub :: Int -> Int -> Binder -> Binder
> updateBinderByIndexSub idx pos [] = []
> updateBinderByIndexSub idx pos (x@(idx',(b,e):rs):xs)
>     -- | pos `seq` idx `seq` idx' `seq` xs `seq` False = undefined
>     | idx == idx' = if pos == (e + 1)
>                     then (idx', (b, e+ 1):rs):xs
>                     else if pos > (e + 1) 
>                          then (idx', (pos,pos):(b, e):rs):xs
>                          else error "impossible, the current letter position is smaller than the last recorded letter"
>     | otherwise = -- idx `seq` pos `seq` xs `seq` 
>                    x:(updateBinderByIndexSub idx pos xs)
> updateBinderByIndexSub idx pos (x@(idx',[]):xs)
>     -- | pos `seq` idx `seq` idx' `seq` xs `seq` False = undefined
>     | idx == idx' = ((idx', [(pos, pos)]):xs)
>     | otherwise = -- idx `seq` pos `seq` xs `seq`  
>                   x:(updateBinderByIndexSub idx pos xs)
> -} 
> {-
> {-| Function 'pdPat0' is the 'abstracted' form of the 'pdPat' function
>     It computes a set of pairs. Each pair consists a 'shape' of the partial derivative, and
>     an update function which defines the change of the pattern bindings from the 'source' pattern to 
>     the resulting partial derivative. This is used in the compilation of the regular expression pattern -}
> pdPat0 :: Pat  -- ^ the source pattern
>           -> Letter -- ^ the letter to be "consumed"
>           -> [(Pat, Int -> Binder -> Binder)]
> pdPat0 (PVar x w p) (l,idx) 
>     | hasBinder p = 
>         let pfs = pdPat0 p (l,idx)
>         in g `seq` pfs `seq` [ (PVar x [] pd, (\i -> (g i) . (f i) )) | (pd,f) <- pfs ]
>     | otherwise = -- p is not nested
>         let pds = partDeriv (strip p) l
>         in g `seq` pds `seq` if null pds then []
>                              else -- not PCRE [ (PVar x [] (PE (resToRE pds)), g) ]
>                                   [ (PVar x [] (PE pd), g) | pd <- pds ]
>     where g = updateBinderByIndex x 
> {-
>     | IM.null (toBinder p) = -- p is not nested
>         let pds = partDeriv (strip p) l
>         in g `seq` pds `seq` if null pds then []
>                              else [ (PVar x [] (PE (resToRE pds)), g) ]
>     | otherwise = 
>         let pfs = pdPat0 p (l,idx)
>         in g `seq` pfs `seq` [ (PVar x [] pd, (\i -> (g i) . (f i) )) | (pd,f) <- pfs ]
>     where g = updateBinderByIndex x 
> -}
> pdPat0 (PE r) (l,idx) = 
>     let pds = partDeriv r l
>     in  pds `seq` if null pds then []
>                   else [ (PE (resToRE pds), ( \_ -> id ) ) ]
> pdPat0 (PStar p g) l = let pfs = pdPat0 p l
>                        in pfs `seq` [ (PPair p' (PStar p g), f) | (p', f) <- pfs ]
> pdPat0 (PPair p1 p2) l = 
>     if (posEpsilon (strip p1))
>     then if isGreedy p1
>          then nub2 ([ (PPair p1' p2, f) | (p1' , f) <- pdPat0 p1 l ] ++ (pdPat0 p2 l))
>          else nub2 ((pdPat0 p2 l) ++ [ (PPair p1' p2, f) | (p1' , f) <- pdPat0 p1 l ])
>     else [ (PPair p1' p2, f) | (p1',f) <- pdPat0 p1 l ]
> pdPat0 (PChoice ps g) l = 
>      nub2 (concatMap (\p -> pdPat0 p l) ps) -- nub doesn't seem to be essential


> nub2 :: Eq a => [(a,b)] -> [(a,b)]
> nub2 = nubBy (\(p1,f1) (p2, f2) -> p1 == p2) 


> {-| Function 'pdPat0Sim' applies simplification to the results of 'pdPat0' -}
> pdPat0Sim :: Pat -- ^ the source pattern 
>              -> Letter -- ^ the letter to be "consumed"
>              -> [(Pat, Int -> Binder -> Binder)]
> pdPat0Sim p l = 
>      let pfs = pdPat0 p l
>          pfs' = pfs `seq` map (\(p,f) -> (simplify p, f)) pfs
>      in nub2 pfs'
> -}


> -- | mainly interested in simplifying epsilon, p --> p
> -- could be made more optimal, e.g. (epsilon, epsilon) --> epsilon
> instance Simplifiable Pat where
>     -- simplify :: Pat -> Pat
>     simplify (PVar i rs p) = PVar i rs (simplify p)
>     simplify (PPair p1 p2) =
>         let p1' = simplify p1
>             p2' = simplify p2
>         in if isEps p1'
>            then p2'
>            else if isEps p2'
>                 then p1'
>                 else PPair p1' p2'
>     simplify (PChoice ps g) =
>         let ps' = filter (not . isPhi) (map simplify ps)
>         in  PChoice ps' g
>     simplify (PStar p g) = PStar (simplify p) g
>     simplify (PPlus p1 p2) = PPlus (simplify p1) (simplify p2)
>     simplify (PE r) = PE (map simplify r)


> instance IsEps Pat where
>    isEps (PVar _ _ p) = isEps p
>    isEps (PE rs) = all isEps rs                                                        
>    isEps (PPair p1 p2) =  (isEps p1) && (isEps p2)
>    isEps (PChoice ps _) =  all isEps ps
>    isEps (PStar p _) = isEps p
>    isEps (PPlus p1 p2) = isEps p1 && isEps p2
>    isEps (PEmpty _) = True
                                                        

> instance IsPhi Pat where
>    isPhi (PVar _ _ p) = isPhi p
>    isPhi (PE rs) = all isPhi rs                                                        
>    isPhi (PPair p1 p2) =  (isPhi p1) || (isPhi p2)
>    isPhi (PChoice ps _) =  all isPhi ps
>    isPhi (PStar p _) = False
>    isPhi (PPlus p1 p2) = isPhi p1 || isPhi p2
>    isPhi (PEmpty _) = False



