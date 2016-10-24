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
import Text.Regex.Deriv.Diagnosis.Ambiguity (deriv,simp,diagnoseRE)
import Text.Regex.Deriv.Diagnosis.Universality (allDerivs, universal, ascii)


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
