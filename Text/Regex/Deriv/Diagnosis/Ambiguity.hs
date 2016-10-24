{-# LANGUAGE GADTs #-} 
module Text.Regex.Deriv.Diagnosis.Ambiguity 
       ( re2dot
       , diagnoseU
       , diagnose
       , diagnoseRE
       , deriv
       , simp
       ) where

import Data.List 
import Data.Char
import Data.Maybe 
import qualified Data.Map as M

import Text.Regex.Deriv.RE
import Text.Regex.Deriv.Common
import Text.Regex.Deriv.Pretty
import Text.Regex.Deriv.IntPattern (strip)
import Text.Regex.Deriv.Parse

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


flatU :: U -> String
flatU Nil = ""
flatU EmptyU = ""
flatU (Letter l) = [l]
flatU (AltU _ u) = flatU u
flatU (Pair (u1,u2)) = flatU u1 ++ flatU u2
flatU (List us) = concatMap flatU  us

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
mkEmptyUs Any            = []
mkEmptyUs (Not _)        = []
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
injDs (Seq r1 r2) (Choice ((Seq rd1 _):_) gf) l (AltU 0 u) =  -- Choice must be binary b/c of deriv2
  let Pair (u', u'') = u 
  in [ Pair (us1, u'') | us1 <- injDs r1 rd1 l u'] 
injDs (Seq r1 r2) (Choice [_,rd2] gf) l (AltU 1 u) =  -- Choice must be binary b/c of deriv2
  [ Pair (us1, us2) | us1 <- mkEmptyUs r1, us2 <- injDs r2 rd2 l u] 
injDs (Seq r1 r2) (Choice [] gf) l u = error " not possible, parse tree and regexp out of sync"
injDs (Seq r1 r2) (Seq rd1 _) l (Pair (u',u'')) = 
  [Pair (us, u'') | us <- injDs r1 rd1 l u']
injDs (Choice (r:rs) _) (Choice (rd:rds) _) l (AltU 0 u) = 
  [ AltU 0 us | us <- injDs r rd l u ] 
injDs (Choice (r:rs) gf) (Choice (rd:rds) gf') l (AltU n u) =  
  [ AltU (n'+1) us | (AltU n' us) <- injDs (Choice rs gf) (Choice rds gf') l (AltU (n-1) u) ] 
injDs (L l') Eps l EmptyU 
  | l == l' = [Letter l]
  | otherwise = error "impossible"
injDs Any Eps l EmptyU = [Letter l]
injDs (Not cs) Eps l EmptyU 
  | not (l `elem` cs) = [Letter l]
  | otherwise = error "impossible"
-- injDs r1 r2 l u = error $ (pretty r1) ++ " --> " ++ (pretty r2) ++ (show u)

testAmbigCase1 r = nullable r && (length $ mkEmptyUs r) > 1

--
-- u -> [u] coerce simplified parse tree back to the original parse tree

-- simplify and return the re
simp :: RE -> RE 
simp r = let (r',_,_) = simp3 r in r'

-- simplify and return the boolean flag indicating whether A2 is applied
simpAmbig :: RE -> Bool
simpAmbig r = let (_,_,b) = simp3 r in b

simp3 :: RE -> (RE, U -> [U], Bool)
simp3 = fixs3 simpStep 


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
rmAltPhi r = (r, \u -> [u]) -- todo check why ex1 need this ?
-- rmAltPhi r = error ("impossible rmAltPhi case:" ++ (pretty r))

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

rep :: Int -> (U -> U) -> U -> U
rep 0 op v = v
rep n op v = rep (n-1) op (op v)

flatChoice :: RE -> (RE, U ->[U])
flatChoice (Choice [] gf) = (Choice [] gf, \u -> [u])
flatChoice (Choice (r@(Choice rsI _):rs) gf) = -- ignoring the inner greedy flag?
  let (Choice rs' _, f) = flatChoice (Choice rs gf)
      l = length rsI
      g = \u -> case u of 
        { AltU n v | n < l     -> [AltU 0 (AltU n v)]
                   | otherwise -> [right w | w <- f $ rep l unRight u ] }
  in (Choice (rsI ++ rs') gf, g)
flatChoice (Choice (r:rs) gf) = 
  let (Choice rs' _, f) = flatChoice (Choice rs gf)
      g = \u -> case u of 
        { AltU 0 v -> [ AltU 0 v ] 
        ; AltU n v -> [ right w | w <- f (unRight u) ]
        } 
  in (Choice (r:rs') gf, g)
     
{-
(a + (b + a + c) + c) ~~> a + b + a + c + c
AltU 1 (AltU 0 'b') <-- AltU 1 'b'
-}

e4 = Choice [L 'a', Choice [L 'b', L 'a', L 'c'] Greedy, L 'c'] Greedy
v4' = AltU 1 (Letter 'b')


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




-- | Build a Finite State Transducer from a RE

data FSX = FSX { start :: RE,
                 final :: [RE],
                 states :: [RE],
                 transitions :: [(RE,Char,RE,U->[U])],
                 ambig1 :: [RE],
                 ambig2 :: [(RE,Char,RE)],
                 ambig3 :: [(RE,Char,RE)] }

buildFSX :: RE -> FSX
buildFSX r = 
  let sig = sigmaRE r
      
      -- building the possible transitions given a re and a char
      mkTransitions :: RE -> Char -> [ (RE, Char , RE, U ->[U]) ]
      mkTransitions r l = 
        let d = deriv r l 
            (r'',fSimp, _ ) = simp3 d
        in [(r, l, r'', \u -> nub $ concat [ injDs r d l u' | u' <- fSimp u ]) | not (isPhi r'')]
           
      -- main iteration
      go :: ([RE], FSX) -> [RE] -> FSX
      go (rs, fsx) curr_rs = 
        let new_ts = concat $ map (\(l,r) -> mkTransitions r l)
                         [ (l,r) | r <- curr_rs, 
                                   l <- sig ]

            new_rs = nub [ r | (_,_,r,_) <- new_ts,
                               not (isPhi r) && not (elem r rs) ]

            -- record ambiguous state A1
            new_ambig1 = filter (\r -> testAmbigCase1 r) rs

            
            -- record ambiguous transition A2
            new_ambig2 = map fst $ filter (\((_,_,r),b) -> b && (not (isPhi r)) ) $
                              [ ((r,l,simp $ deriv r l), snd $ deriv2 r l) | r <- rs, l <- sig ]


            -- record ambiguous transition A3
            new_ambig3 = map fst $ filter (\((_,_,r),b) -> b && (not (isPhi r))) $
                            [ ((r,l,simp (deriv r l)), simpAmbig (deriv r l)) | r <- rs, l <- sig ]
            
            {-

            -- optimization
            dfs  = [ deriv2 r l | r <- rs, l <- sig]
            new_ambig2 = map fst $ filter (\((_,_,r),b) -> b && (not (isPhi r)) ) $
                              [ ((r,l,simp $ fst df), snd df) | df <- dfs ] 

            new_ambig3 = map fst $ filter (\((_,_,r),b) -> b && (not (isPhi r))) $
                            [ ((r,l,simp $ fst df), simpAmbig $ fst df ) | df <- dfs ]
            -}

            new_fsx = FSX { start = start fsx,
                            final = (final fsx) ++ filter nullable new_rs,
                            states = (states fsx) ++ new_rs,
                            transitions = (transitions fsx) ++ new_ts,
                            ambig1 = nub $ ambig1 fsx ++ new_ambig1,
                            ambig2 = nub $ ambig2 fsx ++ new_ambig2,
                            ambig3 = nub $ ambig3 fsx ++ new_ambig3 }

        in if length new_rs == 0
           then new_fsx
           else go (rs ++ new_rs, new_fsx) new_rs 

  in let fsx = FSX { start = r,
                     final = if nullable r then [r] else [],
                     states = [r],
                     transitions = [],
                     ambig1 = [],
                     ambig2 = [],
                     ambig3 = [] }
     in go ([r],fsx) [r]


                  
instance Show AmbigTrans where
  show (A1 (r,c,t,_,s)) = "A1 " ++ show (r,c,t)
  show (A2 (r,c,t,_,s)) = "A2 " ++ show (r,c,t)  
  show (A3 (r,c,t,_,s)) = "A3 " ++ show (r,c,t)
                         


-- | Build fsx graph as dot file, including mapping of numerical state names to underlying expressions (descendants)
buildGraph r =
  let fsx = buildFSX r
      st = zip (states fsx) [1..]
      state r = show $ fromJust $ lookup r $ zip (states fsx) [1..]

      dottedA23 t 
        | elem t (ambig2 fsx ++ ambig3 fsx) = " style = dotted"
        | otherwise                         = ""

      fillcolorA1 s
        | elem s (ambig1 fsx) = " style = filled fillcolor = grey" 
        | otherwise           = ""

      kind s
        | elem s (ambig2 fsx) && elem s (ambig3 fsx) = "|2-3"
        | elem s (ambig2 fsx)                        = "|2"
        | elem s (ambig3 fsx)                        = "|3"
        | otherwise                                  = ""

      escape s@(['\\']) = ['\\'] ++ s
      escape s@(['"']) = ['\\'] ++ s
      escape s@([']']) = ['\\'] ++ s
      escape s@(['[']) = ['\\'] ++ s
      escape s = s                          

      dot = unlines $ [ "digraph G {"
                      ]
                      ++
                      [ "rankdir = LR;"]   -- left to right
                      ++
                      [ state r1 ++ " -> " ++ state r2
                                           ++ "[label=" ++ "\"" ++ escape [c] ++ kind (r1,c,r2) ++ "\"" ++ " " ++ dottedA23 (r1,c,r2) ++ "];"
                        | (r1,c,r2,_) <- transitions fsx
                      ]
                      ++
                      [
                         " 0 -> " ++ state (start fsx) ++ ";"
                       , " 0 [shape = point];"  
                      ]
                      ++
                      [ state r ++ "[shape = circle " ++ fillcolorA1 r ++ " ];"
                        | r <- states fsx, not (nullable r)
                      ]
                      ++
                      [ state r ++ "[shape = doublecircle " ++ fillcolorA1 r ++ " ];"
                        | r <- states fsx, nullable r
                      ]
                      ++
                      [
                        "}"
                      ]

  in (dot, zip (states fsx) [1..])

data AmbigTrans = A1 (RE,Char,RE, U->[U], [(RE,Char,U->[U])]) -- ^ current state, next label, next state(ambig), inj, prefices with state * label * injs
                | A2 (RE,Char,RE, U->[U], [(RE,Char,U->[U])])
                | A3 (RE,Char,RE, U->[U], [(RE,Char,U->[U])])


findMinCounterEx :: FSX -> [U]
findMinCounterEx fsx = 
  let findNextTrans :: RE -> [(RE, Char, RE, U->[U])]
      findNextTrans r = filter (\(s,c,t,f) -> s == r) (transitions fsx)
      
      nub123 :: [(RE,Char,RE, U->[U], [(RE,Char,U->[U])])] -> [(RE,Char,RE, U->[U], [(RE,Char,U->[U])])]
      nub123 = nubBy (\(r1,c1,t1,_,_) (r2,c2,t2,_,_) -> r1 == r2 && c1 == c2 && t1 == t2)

      goUntilAmbig :: [(RE,[(RE,Char,U->[U])])] -> [(RE, Char, RE)] -> Maybe AmbigTrans
      goUntilAmbig curr_states_prefices trans_sofar = 
        let next_trans_prefices = 
              filter (\(s,l,t,f,p) -> not $ (s,l,t) `elem` trans_sofar) $
              nub123 ( concatMap (\(r,prefix) -> 
                                map (\(s,l,t,f) -> (s,l,t,f,prefix)) $ findNextTrans r
                              ) curr_states_prefices )
            ambigs1 = filter (\(s,l,t,f,_) -> t `elem` (ambig1 fsx))       next_trans_prefices
            ambigs2 = filter (\(s,l,t,f,_) -> (s,l,t) `elem` (ambig2 fsx)) next_trans_prefices
            ambigs3 = filter (\(s,l,t,f,_) -> (s,l,t) `elem` (ambig3 fsx)) next_trans_prefices
        in if null next_trans_prefices 
           then Nothing
           else case (ambigs1,ambigs2,ambigs3) of 
             { ((trans:_), _, _)   -> Just $ A1 trans
             ; ([], (trans:_), _)  -> Just $ A2 trans
             ; ([], [], (trans:_)) -> Just $ A3 trans
             ; ([], [], [])        -> -- no ambig found so far
               let next_states_prefices = map (\(r,l,t,f,p) -> (t,p++[(r,l,f)])) next_trans_prefices
               in goUntilAmbig next_states_prefices (trans_sofar ++ (map (\(s,l,t,_,_) -> (s,l,t)) next_trans_prefices))
             }
  in case (goUntilAmbig [(start fsx, [])] []) of 
    { Nothing -> [] 
    ; Just (A1 (r,l,t,f,pf)) -> 
      let ut = genV t
          urs = f ut
          (s,us) = foldl (\(t,us) (r,l,f) -> (r, concat [ f u | u <- us ])) (r,urs) pf
      in us
    ; Just (A2 (r,l,t,f,pf)) -> 
      let ut = genV t
          urs = f ut
          (s,us) = foldl (\(t,us) (r,l,f) -> (r, concat [ f u | u <- us ])) (r,urs) pf
      in us
    ; Just (A3 (r,l,t,f,pf)) -> 
      let ut = genV t
          urs = f ut
          (s,us) = foldl (\(t,us) (r,l,f) -> (r, concat [ f u | u <- us ])) (r,urs) pf
      in us
    }

diagnoseU :: String -> Either String [U]
diagnoseU src = case parsePat src of
  { Left err -> Left $ "Unable to parse regex '" ++ src ++ "'. Error: " ++ show err
  ; Right pat -> 
       let r   = strip(pat)
           fsx = buildFSX r
       in Right $ findMinCounterEx fsx
  }

diagnose :: String -> Either String [String]
diagnose src = case diagnoseU src of 
  { Left err -> Left src
  ; Right us -> Right $ map flatU us
  }
               
diagnoseRE :: RE -> [U]
diagnoseRE r = 
  let fsx = buildFSX r
  in findMinCounterEx fsx


re2dot :: String -> FilePath -> IO ()
re2dot src fp =  case parsePat src of
  { Left err -> return ()
  ; Right pat -> 
       let r     = strip(pat)
           (g,_) = buildGraph r
       in do 
         { writeFile fp g }
  }
  


-- testing corner

-- (a* a*)*
r11 = Star (Seq (Star (L 'a') Greedy) (Star (L 'a') Greedy)) Greedy



-- (a* (a* + a))*
rExFail3 = Star (Seq (Star (L 'a') Greedy)
                (Choice [Star (L 'a') Greedy,L 'a'] Greedy)) Greedy


-- (a* a (a* + a))*
rExFail3b = Star (Seq (Seq (Star (L 'a') Greedy) (L 'a'))
                (Choice [Star (L 'a')  Greedy ,L 'a'] Greedy)) Greedy

-- (a* (a*a + a))*
rExFail3c = Star (Seq (Star (L 'a')  Greedy)
                (Choice [Seq (Star (L 'a')  Greedy) (L 'a') ,L 'a'] Greedy)) Greedy

-- (a a* (a* + a))*
rExFail3d = Star (Seq (Seq (L 'a') (Star (L 'a') Greedy))
                (Choice [Star (L 'a') Greedy,L 'a'] Greedy)) Greedy


derivN :: Int -> Char -> RE -> RE
derivN 0 c r = r
derivN n c r = derivN (n-1) c (simp (deriv r c))

 
{- shows that simp is working
*Text.Regex.Deriv.Ambiguity.Diagnosis> derivN 1 'a' rExFail3
Seq (Choice [Seq (Star (L 'a') ) (Choice [Star (L 'a') ,L 'a'] ),Star (L 'a') ,Eps] ) (Star (Seq (
Star (L 'a') ) (Choice [Star (L 'a') ,L 'a'] )) )



*Text.Regex.Deriv.Ambiguity.Diagnosis> derivN 2 'a' rExFail3
Seq (Choice [Seq (Star (L 'a') ) (Choice [Star (L 'a') ,L 'a'] ),Star (L 'a') ,Eps] ) (Star (Seq (Star (L 'a') ) (Choice [Star (L 'a') ,L 'a'] )) )
*Text.Regex.Deriv.Ambiguity.Diagnosis> derivN 3 'a' rExFail3
Seq (Choice [Seq (Star (L 'a') ) (Choice [Star (L 'a') ,L 'a'] ),Star (L 'a') ,Eps] ) (Star (Seq (Star (L 'a') ) (Choice [Star (L 'a') ,L 'a'] )) )
-}


derivN3 :: Int -> RE -> Char -> (RE, U -> [U], Bool)
derivN3 0 r c = (r, \u -> [u], False)
derivN3 n r c = 
  let (d, b1)     = deriv2 r c
      f           = injDs r d c
      (s, f', b2) = simp3 d
      (r', g, b3) = derivN3 (n-1) s c
  in (r', f .:. f' .:. g, b1 || b2 || b3)

-- (((a)* ((a)*|a))|(a)*|()) (((a)* ((a)*|a)))*
v5' = Pair (AltU 2 EmptyU, 
                           List [Pair (List [Letter 'a'], AltU 0 (List [Letter 'a']))])
v5'' = Pair (AltU 0 (Pair (List [Letter 'a'],AltU 0 (List [Letter 'a']))),
                           List [Pair (List [Letter 'a'],AltU 0 (List [Letter 'a']))])
v5''' = Pair (AltU 1 (List [Letter 'a']),
                           List [Pair (List [Letter 'a'],AltU 0 (List [Letter 'a']))])
{- testing
let (d, b1) = deriv2 rExFail3 'a'
let f = injDs rExFail3 d 'a'
let v5'''' = Pair (AltU 1 (AltU 1 EmptyU),List [Pair (List [Letter 'a'],AltU 0 (List [Letter 'a']))])
tc v5'''' d 
True
f v5'''' 
error!!!


let (s, f', b2) = simp3 d
let (r', g, b3) = derivN3 0 'a' s

-}
-- (((a)* ((a)*|a)))* / a
-- > (((a)* ((a)*|a)))/a  (((a)* ((a)*|a)))*
-- > (((a)*/a ((a)*|a)) | ((a)*|a)/a) (((a)* ((a)*|a)))*
-- > (((() (a*)) ((a)*|a)) | ((() (a)*) | ())) (((a)* ((a)*|a)))*
-- ((((() (a)*) ((a)*|a))|((() (a)*)|())) (((a)* ((a)*|a)))*)

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



-- | t : r              
-- | check whether parse tree t is in type r

tc :: U -> RE -> Bool
tc EmptyU Eps                 = True
tc (Letter c) (L c')          = c == c'
tc (Letter c) Any             = True
tc (Letter c) (Not cs)        = not (c `elem` cs)
tc (Pair (u1,u2)) (Seq r1 r2) = (tc u1 r1) && (tc u2 r2)
tc (AltU n u) (Choice rs gf)  = tc u (rs !! n)
tc (List us) (Star r gf)      = all (\u -> tc u r) us
tc _ _                        = False


-- | 
genV :: RE -> U
genV Eps = EmptyU
genV (L c) = Letter c
genV Any   = Letter 'a'
genV (Not cs) = Letter $ head (filter (\c -> not (c `elem` cs)) (map chr [0..255]))
genV (Seq r1 r2) = Pair (genV r1, genV r2)
genV (Choice rs _) = AltU 0 (genV (head rs))
genV (Star r _) = List []




-- Examples
---------------------------

-- (a a* + b a + a b a)* b
ex1 = Seq (Star (Choice [Seq (L 'a') (Star (L 'a') Greedy), 
                         (Choice [Seq (L 'b') (L 'a'),
                                 Seq (L 'a') (Seq (L 'b') (L 'a'))] Greedy)] Greedy) Greedy)
          (L 'b')

{-
*Text.Regex.Deriv.Ambiguity.Diagnosis> putStrLn $ fst $ buildGraph ex1
digraph G {
rankdir = LR;
1 -> 2[label="a" ];
1 -> 3[label="b" ];
2 -> 4[label="a" ];
2 -> 3[label="b|3"  style = dotted];
3 -> 1[label="a" ];
4 -> 4[label="a|2-3"  style = dotted];
4 -> 3[label="b|2-3"  style = dotted];
 0 -> 1;
 0 [shape = point];
1[shape = circle  ];
2[shape = circle  ];
4[shape = circle  ];
3[shape = doublecircle  ];
}


equivalent to the one found on in the paper prototype DerivAmbigDialKL.hs. 
State 5 was merged with state 1 because we apply Eps . r = r similarity rule
-}


-- same as ex1
ex1' = Seq (Star (Choice [Seq (L 'a') (Star (L 'a') Greedy), Seq (L 'b') (L 'a'),
                                 Seq (L 'a') (Seq (L 'b') (L 'a'))] Greedy) Greedy)
          (L 'b')


{-testing min counter example

*Text.Regex.Deriv.Diagnosis.Ambiguity> let fsx = buildFSX ex1
*Text.Regex.Deriv.Diagnosis.Ambiguity> findMinCounterEx fsx


-}