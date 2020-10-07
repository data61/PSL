{-
Author:  Christian Sternagel <c.sternagel@gmail.com> (2017)
License: LGPL
-}
module Main (main) where

import HLDE -- for solve: computing solutions to homogeneous linear diophantine equations
import System.Environment -- for getArgs
import System.IO -- for file reading
import System.Exit -- for error codes
import System.Directory -- for doesFileExist

main = getArgs >>= parse

parse [] = do
  input <- getContents
  start input
parse ["--help"] =  do
  hPutStrLn stdout usage
  exitWith ExitSuccess
parse [s] = do
  b <- doesFileExist s
  if b then do
    input <- readFile s
    start input
  else
    start s
parse _ = do
  hPutStrLn stderr usage
  exitWith (ExitFailure 1)

start input = do
  let (a, b) = read input :: ([Integer], [Integer])
  if 0 `elem` a || 0 `elem` b then do
    hPutStrLn stderr "0-coefficients are not allowed"
    exitWith (ExitFailure 2)
  else if null a || null b then do
    hPutStrLn stderr "empty lists of coefficients are not allowed"
    exitWith (ExitFailure 3)
  else
    mapM_ (putStrLn . show . (\(x, y) -> (map integer_of_nat x, map integer_of_nat y))) $
      solve (map nat_of_integer a) (map nat_of_integer b)

usage = "usage: hlde [string]\n\
        \  \n\
        \  If a string argument is given and a file of the same name exists\n\
        \  then read from this file, if no such file exists read directly from\n\
        \  the given string, and otherwise read from stdin.\n\
        \  \n\
        \  As input a pair of lists of coefficients is expected (representing a\n\
        \  homogeneous linear Diophantine equation, or HLDE for short). E.g.\n\
        \  \n\
        \    ([1,1],[2])\n\
        \  \n\
        \  corresponds to the HLDE\n\
        \  \n\
        \    x1 + x2 = 2*y1"

