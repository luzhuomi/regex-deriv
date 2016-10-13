{-# LANGUAGE GADTs #-} 
module Text.Regex.Deriv.Ambiguity.Diagnosis where

import Text.Regex.Deriv.RE
import Text.Regex.Deriv.Common
import Data.List 
import qualified Data.Map as M
-- Parse tree representation
data U where
  Nil :: U
  EmptyU :: U
  Letter :: Char -> U
  AltU :: Int -> U -> U 
  -- LeftU u, Right Left u, ... 
  -- AltU 0 u, AltU 1 u, ...
  -- Note: Right Right _ is never used, because it is the value of Phi,
  --  e.g. r1+r2+r3+phi ~> Alt [r1,r2,r3]
  Pair :: (U,U) -> U
  List :: [U] -> U
   deriving (Show, Eq)
-- todo any & not

-- | Nullable check
nullable :: RE -> Bool
nullable = posEps

-- | Derivative operation.
-- Additional boolean result value to report if case A2 arises.
deriv2 :: RE -> Char -> (RE, Bool)
deriv2 Phi l = (Phi, False)
deriv2 Eps l = (Phi, False)
deriv2 Any l = (Eps, False)
deriv2 (Not ls) l | l `elem` ls = (Phi, False)
                  | otherwise   = (Eps, False)
deriv2 (L l') l
    | l == l'   = (Eps, False)
    | otherwise = (Phi, False)
deriv2 (Choice rs gf) l = 
     let rbs = map (\r -> deriv2 r l) rs
         (rs', bs) = unzip rbs
     in (Choice rs' gf, any (== True) bs)
deriv2 (Seq r1 r2) l
    | nullable r1 = 
         let (r1', b1) = deriv2 r1 l
             (r2', b2) = deriv2 r2 l
         in (Choice [Seq r1' r2, r2'] Greedy, b1 || b2 || testAmbigCase1 r1) -- A2
    | otherwise = 
         let (r1', b1) = deriv2 r1 l
         in (Seq r1' r2, b1)
deriv2 (Star r gf) l = 
        let (r', b) = deriv2 r l
        in (Seq r' (Star r gf), b)


deriv :: RE -> Char -> RE
deriv r c = fst $ deriv2 r c


-- | For a nullable expression, compute all empty parse trees.
mkEmptyUs :: RE -> [U]
mkEmptyUs Phi            = []
mkEmptyUs Eps            = [EmptyU]
mkEmptyUs (L l)          = []
mkEmptyUs (Choice rs _) =
  let idxed_rs = zip [0..] rs
  in [ AltU idx u | (idx, r) <- idxed_rs, u <- mkEmptyUs r, nullable r]
mkEmptyUs (Seq r1 r2)   = 
       [ Pair (u1,u2) | u1 <- mkEmptyUs r1, u2 <- mkEmptyUs r2 ]
mkEmptyUs (Star r _)      = [List []]

-- | Injection to obtain r's parse trees from the parse tree of the derivative.
injDs :: RE -> RE -> Char  -> U -> [U]
injDs (Star r _) (Seq rd _) l (Pair (u, List us)) = 
  [ List (u1:us) | u1 <- injDs r rd l u ] 
injDs (Seq r1 r2) (Choice ((Seq rd1 _):_) gf) l (AltU 0 u) = 
  let Pair (u', u'') = u 
  in [ Pair (us1, u'') | us1 <- injDs r1 rd1 l u'] 
injDs (Seq r1 r2) (Choice (_:rd2) gf) l (AltU n u) = 
  [ Pair (us1, us2) | us1 <- mkEmptyUs r1, us2 <- injDs r2 (Choice rd2 gf) l (AltU (n-1) u)] 
injDs (Seq r1 r2) (Choice [] gf) l (AltU n u) = error " not possible, parse tree and regexp out of sync"
injDs (Seq r1 r2) (Seq rd1 _) l (Pair (u',u'')) = 
  [Pair (us, u'') | us <- injDs r1 rd1 l u']
injDs (Choice (r:rs) _) (Choice (rd:rds) _) l (AltU 0 u) = 
  [ AltU 0 us | us <- injDs r rd l u ] 
injDs (Choice (r:rs) gf) (Choice (rd:rds) gf') l (AltU n u) =  
  [ AltU (n'+1) us | (AltU n' us) <- injDs (Choice rs gf) (Choice rds gf') l (AltU (n-1) u) ] 
injDs (L l') Eps l EmptyU 
  | l == l' = [Letter l]
  | otherwise = error "impossible"


testAmbigCase1 r = nullable r && (length $ mkEmptyUs r) > 1

--
-- u -> [u] coerce simplified parse tree back to the original parse tree

simp :: RE -> (RE, U -> [U], Bool)
simp = fixs3 simpStep 


fixs3 :: (RE -> (RE, U -> [U], Bool)) -> RE -> (RE, U -> [U], Bool)
fixs3 trans r = 
  let (r',f,b) = trans r
  in if r == r'
     then (r',f,b)
     else let (r'', g, b2) = fixs3 trans r'
          in (r'', \u -> nub $ concat [ f u' | u' <- g u], b || b2 )
             
fix2 :: (RE -> (RE, U -> U)) -> RE -> (RE, U -> U)
fix2 trans r = 
  let (r',f) = trans r
  in if r == r'
     then (r', f)
     else let (r'', g) = fix2 trans r'
          in (r'', f . g)


fixs2 :: (RE -> (RE, U -> [U])) -> RE -> (RE, U -> [U])
fixs2 trans r = 
  let (r',f) = trans r
  in if r == r'
     then (r', f)
     else let (r'', g) = fixs2 trans r'
          in (r'', f .:. g)



simpStep :: RE -> (RE, U -> [U], Bool) 
simpStep (Seq Eps r) =  
  let (r', f, b) = simpStep r
  in (r', \u -> nub [Pair (EmptyU,v) | v <- f u], b)
simpStep (Seq Phi r) = (Phi, undefined, False)
simpStep (Choice [r] gf) = (r, \u -> [AltU 0 u], False) -- todo
simpStep (Choice rs gf)  = 
  let rfbs            = map simpStep rs 
      (rs1, fs1, bs1) = unzip3 rfbs
      f1 :: U -> [U] 
      f1 (AltU n v)   = [AltU n u | u <- (fs1 !! n) v]
      f1 u            = [u]
      b1              = any (== True) bs1
      (r2, f2)        = rmAltPhi (Choice rs1 gf)
      (r3, f3)        = flat r2 
      (r4, f4, b4)    = (fixs3 nubChoice) r3
  in (r4, f1 .:. f2 .:. f3 .:. f4, b1 || b4) 
      -- (rs3, f3, b3)   = nubs rs1
      -- (r4, f4, b4)    = (simpDist simpStep) r3
  -- in (r4, f1 .:. f2 .:. f3 .:. f4, b1 || b3 || b4) -- todo
simpStep (Seq r1 r2)      = 
  let (r1',f1, b1) = simpStep r1 
      (r2',f2, b2) = simpStep r2
      f = \u -> case u of 
        { Pair (u1,u2) -> [ Pair (u1',u2') | u1' <- f1 u1, u2' <- f2 u2] }
  in (Seq r1' r2', f, b1 || b2)
simpStep r = (r, \u ->[u], False)     


-- | add a right tag
right :: U -> U
right (AltU x u) = AltU (x+1) u
right u          = u

-- | remove a right tight
unRight :: U -> U
unRight (AltU 0 u) = error " unRight is applied to a Left v "
unRight (AltU x u) = AltU (x-1) u
unRight v          = v


-- parse tree transformer composition
(.:.) :: (U -> [U]) -> (U -> [U]) -> U -> [U]
(.:.) f g = \u -> concat [ f v | v <- g u ]


rmAltPhi :: RE -> (RE, U -> [U])
rmAltPhi r@(Choice [r'] gf) = (r, \u -> [u])
rmAltPhi (Choice (r:rs) gf) = 
  let (fs,rs') = unzip (rmAltPhiN 0 (r:rs))
      g = \u -> case u of { AltU n v -> [(fs !! n) u] }
  in (Choice rs' gf, g)

rmAltPhiN :: Int -- ^ num pos to shift to the right == num of phi found so far
             -> [RE] -> [(U -> U, RE)]
rmAltPhiN _ [] = []
rmAltPhiN n (r:rs) | isPhi r = rmAltPhiN (n+1) rs
                   | otherwise = (\(AltU m v) -> (AltU (n+m) v), r):(rmAltPhiN n rs)
{- 
phi + a + phi + b ~~> a + b

Alt 1 a         <- Alt 0 a
Alt 3 b         <- Alt 1 b

-} 
e1 = Choice [Phi, L 'a', Phi, L 'b'] Greedy
e1' = Choice [L 'a', L 'b'] Greedy
v1' = AltU 0 (Letter 'a')
 -- todo need more test


-- flatten a nested choice
flat :: RE -> (RE, U -> [U]) 
flat = fixs2 flatStep

flatStep :: RE -> (RE, U -> [U])
flatStep (Seq r1 r2) = 
  let (r1',f1) = flatStep r1
      (r2',f2) = flatStep r2
      f = \u -> case u of 
        { Pair (u1,u2) -> [ Pair (u1',u2') | u1' <- f1 u1, u2' <- f2 u2 ] }
  in (Seq r1' r2', f)
flatStep (Choice rs gf) = flatChoice (Choice rs gf)      

flatChoice :: RE -> (RE, U ->[U])
flatChoice (Choice [] gf) = (Choice [] gf, \u -> [u])
flatChoice (Choice (r@(Choice rsI _):rs) gf) = -- ignoring the inner greedy flag?
  let (Choice rs' _, f) = flatChoice (Choice rs gf)
      l = length rsI
      g = \u -> case u of 
        { AltU n v | n < l     -> [AltU 0 (AltU n v)]
                   | otherwise -> [AltU (n - l) v] }
  in (Choice (rsI ++ rs') gf, g .:. f)
flatChoice (Choice (r:rs) gf) = 
  let (Choice rs' _, f) = flatChoice (Choice rs gf)
      g = \u -> case u of 
        { AltU 0 v -> [ AltU 0 v ] 
        ; AltU n v -> [ right w | w <- f (AltU n v) ]
        } 
  in (Choice (r:rs') gf, g)
     



nubChoice :: RE -> (RE, U -> [U], Bool)
-- subsumed by simpAltPhi
-- nubChoice (Choice [r1, r2] gf) | isPhi r1 = (r2, \u -> [AltU 1 u], False) 
-- nubChoice (Choice [r1, r2] gf) | isPhi r2 = (r1, \u -> [AltU 0 u], False)
nubChoice (Choice [r1, r2] gf) | r1 == r2 = (r1, \u -> [AltU 0 u, AltU 1 u], not $ isPhi r1)
nubChoice r@(Choice _ _)      = 
  let (r', f, m, idx, b) = nubChoiceWith r 0 M.empty 
  in (r', f, b)
nubChoice r = (r, \u ->[u], False) -- todo: why this is needed?
                                                                                        
-- | a global nub, e.g. (r1+r2+r3+r1) ---> (r1+r2+r3)
-- | prereq: the input re choice must be in right assoc form
-- | the second para of type Int keep track of the position of the current choice option
-- | the third para of type Map RE [Int] keep tracks of the list of unique options that we have seen starting from the left most, the payload of type [Int]
-- | captures the positions of the original/duplicate copy of the choice.
nubChoiceWith :: RE -> Int -> M.Map RE [Int] -> (RE, U -> [U], M.Map RE [Int], Int, Bool)
nubChoiceWith (Choice (r1:rs) gf) idx m = 
  case M.lookup r1 m of 
    { Just idxs -> 
         -- r1 \in M    M |- r2...rN --> r2'...rM'
         -- -----------------------------
         -- M |- r1 + r2...rN --> r2'...rM'
         let m' = M.update (\_ -> Just (idxs ++[idx])) r1 m
             (Choice rs' _, g, m'', idx', b) = nubChoiceWith (Choice rs gf) (idx+1) m'
             f = \u -> [right v | v <- g $ unRight u ]
         in (Choice rs' gf, f, m'', idx', not $ isPhi r1)
-- TRICKY: use not $ isPhi r1 instead of True
-- elminating phi doesn't lead to ambiguities            
    ; Nothing -> 
           -- r1 \not \in M   M U {r1} |- r2...rN --> r2'...rM'
           -- ---------------------------------------
           -- M |- r1 + r2 --> r1 + r2'...rM'
           let m' = M.insert r1 [idx] m
               (Choice rs' _, g, m'', idx', b) = nubChoiceWith (Choice rs gf) (idx+1) m'
               idxs = ( case M.lookup r1 m'' of -- check
                           { Nothing -> [] 
                           ; Just idxs' -> idxs' } )
               f = \u -> case u of
                 { AltU 0 v -> map (\i -> mkCons (i - idx) v) idxs
                 ; AltU n v -> [right w | w <- g $ unRight u] 
                 }
           in (Choice (r1:rs') gf, f, m'', idx', b)           
    }
nubChoiceWith (Choice [] gf) idx m = (Choice [] gf, \u -> [u], m, idx, False)  
nubChoiceWith r idx m = (r, \u -> [u], m, idx, False) -- todo: why this is needed

{-
a + b + c + a --> a + b + c
AltU 0 a, Alt 3 a  <--  AltU 0 a
AltU 1 b           <--  AltU 1 b
-}

e2 = Choice [L 'a', L 'b', L 'c', L 'a'] Greedy
v2' = AltU 0 (Letter 'a')
v2'' = AltU 1 (Letter 'b')

e3 = Choice [L 'a', L 'b', L 'c'] Greedy
{-
a + b + c  --> a + b + c
AltU 0 a           <--  AltU 0 a
AltU 1 b           <--  AltU 1 b
-}

-- | mkCons 0 = L 
-- | mkCons 1 = R L
-- | mkCons 2 = R R L
mkCons :: Int -> U -> U 
mkCons n | n <=0 = AltU 0
         | otherwise = AltU n 


-- (a* a*)*
r11 = Star (Seq (Star (L 'a') Greedy) (Star (L 'a') Greedy)) Greedy




-- no need to sort, nubchoice will dedup without changing the order
{-
-- | Sort RE in right associative normal form via bubble sort
sortChoice :: RE -> (RE, U -> U)
sortChoice (Choice [r1,r2] gf)
    | r1 <= r2 = (Choice [r1,r2] gf, \u -> u)
    | otherwise = (Choice [r2,r1] gf, \u -> case u of
                                        AltU 0 u2 -> AltU 1 u2
                                        AltU 1 u1 -> AltU 0 u1)
sortChoice (Choice (r1:r2:r3) gf)
    | r1 <= r2 = let (Choice r23 _, f) = sortChoice (Choice (r2:r3) gf)
                 in (Choice (r1:r23) gf,
                     \u -> case u of
                            AltU 0 u1 -> AltU 0 u1 
                            AltU i23 u23 -> right $ f (AltU (i23 - 1) u23))
    | otherwise = (Choice (r2:r1:r3) gf,
                   \u -> case u of
                          AltU 0 u2 -> AltU 1 u2
                          AltU 1 u1 -> AltU 0 u1
                          AltU n u ->  AltU n u)
sortChoice r = (r, \u -> u)
-}


{-

let (d1, f1) = deriv2 r11 'a'
let (s1, f1', b1) = simp d1
let (d2, f2) = deriv2 s1 'a'
let (r2, f2', b2) = simp d2
-}



-- | removes duplicate in choice
-- e.g.
-- (a + (b + (a + c))) ~> 



{-
nubs :: [RE] -> ([RE], U -> [U], Bool)
nubs [] = ([], undefined, False)
nubs [r] = ([r], \u -> [u], False)

nubs (r:rs) = nubsN 0 (r:rs)

nubsN :: Int -> [RE] -> ([RE], U -> [U], Bool)
nubsN _ []  = ([], undefined, False)
nubsN _ [r] = ([r], \u -> [u], False)
nubsN pos (r:rs) = 
  case r `elems` rs of 
    { Just idx -> -- found duplicate
         let (rs', f, b) = nubsN (pos+1) rs
             dup_pos     = idx + pos
             g = \u -> case u of 
               { AltU n v | n == dup_pos -> [AltU n-idx v, AltU n v]
                          | otherise     -> [AltU n v]
               }
         in (rs', g .:. f, True)
    ; Nothing -> 
           let (rs', f, b) = nubsN (pos+1) rs 
               g = \u -> case u of 
                 { AltU n v -> [AltU n v]  }
           in (r:rs', 
-}               
                

simpDist :: ( RE -> (RE, U -> [U], Bool))  ->  RE -> (RE, U -> [U], Bool)
simpDist = undefined
  