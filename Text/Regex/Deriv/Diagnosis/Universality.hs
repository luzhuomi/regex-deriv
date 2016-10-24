module Text.Regex.Deriv.Diagnosis.Universality where

-- Universality test
-- Let deriv+(sigma*)(r) denotes all non-direct derivative descandants of r
-- We say r is universal iff for all t \in deriv+(sigma*), () \in t

import Data.List 
import Data.Char
import Data.Maybe 
import qualified Data.Map as M

import Text.Regex.Deriv.RE
import Text.Regex.Deriv.Common
import Text.Regex.Deriv.Pretty
import Text.Regex.Deriv.IntPattern (strip)
import Text.Regex.Deriv.Parse
import Text.Regex.Deriv.Diagnosis.Ambiguity (deriv,simp)
-- import System.IO.Unsafe (unsafePerformIO)

-- ^ compute deriv(sigma*)(r)

allDerivs :: [Char] -> RE -> [RE] 
allDerivs sigma r = go [] [r] 
  where go :: [RE] -> [RE] -> [RE]
        go sofar [] = sofar
        go sofar rs = 
          let rs' = nub $ filter (\r -> not (r `elem` sofar)) $ 
                    (concatMap (\r -> [ simp $ deriv r l | l <- sigma ]) rs)
          in go (nub (sofar ++ rs)) rs'
             

universal :: [Char] -> RE -> Bool 
universal sigma r = all posEps (allDerivs sigma r)
          
                   
ascii :: [Char]                    
ascii = map chr [0..255]