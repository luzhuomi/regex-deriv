module Text.Regex.Deriv.Diagnosis.Evil where

-- Evil test
-- Let deriv(sigma*)(r) denotes all derivative descandants of r
--  nrderiv(sigma*)(r) denotes the non-reflexive descandants.
-- We say r is evil iff there exists r' in deriv(sigma*)(r) such that
--   1) r' is ambigous and 
--   2) r' in dderiv(sigma*)(r') and
--   3) there not exits r'' in deriv(sigma*)(r') such that r'' is universal


import Data.List 
import Data.Char
import Data.Maybe 
import qualified Data.Map as M

import Text.Regex.Deriv.RE
import Text.Regex.Deriv.Common
import Text.Regex.Deriv.Pretty
import Text.Regex.Deriv.IntPattern (strip)
import Text.Regex.Deriv.Parse
import Text.Regex.Deriv.Diagnosis.Ambiguity (deriv,simp,diagnoseRE,flatU, diagnosePrefStr)
import Text.Regex.Deriv.Diagnosis.Universality (allDerivs, universal, ascii)

{-

nrdDerivs :: [Char] -> RE -> [RE] 
nrdDerivs sigma r = 
  nub $ concatMap (\l -> allDerivs sigma (deriv r l)) sigma

evil :: [Char] -> RE -> Bool
evil sigma r = -- todo: optimization needed, deriv(r') should be a subset of deriv(r)
  let allR' = allDerivs sigma r
  in any ambig_loop_no_uni_desc allR'
     where ambig_loop_no_uni_desc :: RE -> Bool 
           ambig_loop_no_uni_desc r' = case diagnoseRE r' of
             { [] -> False
             ; _:_ -> 
               let allR'' = allDerivs sigma r'
                   nrds = nrdDerivs sigma r
               in  (r' `elem` nrds) && all (\t -> not $ universal ascii t ) allR''
             }

diagnose :: String -> Either String Bool
diagnose src = case parsePat src of
  { Left err -> Left $ "Unable to parse regex '" ++ src ++ "'. Error: " ++ show err
  ; Right pat -> 
       let r   = strip(pat)
       in Right $ evil ascii r
  }
               
-- diagnose "^([a-zA-Z0-9_\\.\\-])+\\@(([a-zA-Z0-9\\-])+\\.)+([a-zA-Z0-9]{2,4})+$"               
-- diagnose "^((a|b|(ab))*c|([abcd])*)$"
-}

-- (why partial derivatives? (a+b+ab)*c + sigma*)
-- Evil test
-- Let pderiv(sigma*)(r) denotes all partial derivative descandants of r 
-- We say r is evil iff there exists r' in pderiv(sigma*)(r) such that
--   1) r' is ambigous and 
--   2) r' has an ambiguous prefix p where r' --p--> r'
--   3) r' is not universal


pderiv = partDeriv

allPDerivs :: [Char] -> RE -> [RE]
allPDerivs sigma r = go [] [r] 
  where go :: [RE] -> [RE] -> [RE]
        go sofar [] = sofar
        go sofar rs = 
          let rs' = nub $ filter (\r -> not (r `elem` sofar)) $ 
                    (concatMap (\r -> concat [ map simp $ pderiv r l | l <- sigma ]) rs)
          in go (nub (sofar ++ rs)) rs'
        
        
evil :: [Char] -> RE -> Bool
evil sigma r = -- todo: optimization needed, deriv(r') should be a subset of deriv(r)
  let allR' = allPDerivs sigma r
  in any ambig_loop allR'
    where ambig_loop :: RE -> Bool 
          ambig_loop r' = case diagnosePrefStr r' of
            { [] -> False
            ; str -> (is_a_loop_prefix r' str)&& (not (universal sigma r' ))
            }
          is_a_loop_prefix :: RE -> [Char] -> Bool
          is_a_loop_prefix r p = 
            let d = foldl (\x l -> simp $ deriv x l) r p -- follow the prefix
                    -- check whether r is a descendant of d
            in r `elem` (allDerivs sigma d) 
             
diagnose :: String -> Either String Bool
diagnose src = case parsePat src of
  { Left err -> Left $ "Unable to parse regex '" ++ src ++ "'. Error: " ++ show err
  ; Right pat -> 
       let r   = strip(pat)
       in Right $ evil ascii r
  }
                
a = L 'a'               
b = L 'b'
c = L 'c'
x1 = Seq (Star (Choice [a, b, Seq a b] Greedy) Greedy) c