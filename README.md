regex-deriv
===========

A regular expression library suite based on Brozowski's derivative implemented in Haskell.

The library features 
- Derivative operation of regular expression
- An efficient regular expression parsing and matching algorithm (faithfully) implementing POSIX matching policy.
- An ambiguity regular expression diagnostic tool

installation
============
```
$ cabal configure && cabal build && cabal install
```
matching 
===========
```
module Main where


import Text.Regex.Deriv.ByteString

import System.Environment
import Data.Maybe
import qualified Data.ByteString.Char8 as S


parse compiled s = case regexec compiled s of 
                     (Right (Just (_,_,_,l))) -Just l
                     _ -Nothing


main :: IO ()
main = do 
  { [ p, x ] <- getArgs
  ; let pat = S.pack p
        compiled = case compile defaultCompOpt defaultExecOpt pat of
                   Left _  -error " compilation failed . "
                   Right r -r
  ; ls <-  S.readFile x
  ; let input = if S.null ls  
                then S.empty 
                else head $ S.lines ls
        result = parse compiled input
  ; putStrLn (show result)
  }

```

ambiguity check
=============


