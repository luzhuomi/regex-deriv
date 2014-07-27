> module Main where


> import Text.Regex.Deriv.ByteString

> import System.Environment
> import Data.Maybe
> import qualified Data.ByteString.Char8 as S



> parse compiled s = case regexec compiled s of 
>                      (Right (Just (_,_,_,l))) -> Just l
>                      _ -> Nothing


> main :: IO ()
> main = do 
>   { [ p, x ] <- getArgs
>   ; let pat = S.pack p
>         compiled = {-# SCC "main/compile" #-} case compile defaultCompOpt defaultExecOpt pat of
>                    Left _  -> error " compilation failed . "
>                    Right r -> r
>         -- ls = S.pack "abc"
>   ; ls <- {-# SCC "main/readFile" #-} S.readFile x
>   ; let input = if S.null ls  
>                 then S.empty 
>                 else head $ S.lines ls
>         result = {-# SCC "main/parse" #-} parse compiled input
>   ; putStrLn (show result)
>   }
