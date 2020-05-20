(*
    Authors:    Sebastiaan Joosten
                René Thiemann
*)
subsection \<open>A Haskell Interface to the FPLLL-Solver\<close>

theory FPLLL_Solver
  imports LLL_Certification
begin

text \<open>We define @{const external_lll_solver} via an invocation of the fplll solver.
  For eta we use the default value of fplll, and delta is chosen so that 
  the required precision of alpha will be guaranteed. We use the command-line
  option -bvu in order to get the witnesses that are required for certification.\<close>

text \<open>Warning: Since we only define a Haskell binding for FPLLL, 
  the target languages do no longer evaluate to the same results on @{const short_vector_hybrid}!\<close>

code_printing
  code_module "FPLLL_Solver" \<rightharpoonup> (Haskell) 
\<open>module FPLLL_Solver where {

import System.Process (proc,createProcess,waitForProcess,CreateProcess(..),StdStream(..));
import System.IO.Unsafe (unsafePerformIO);
import System.IO (stderr,hPutStrLn,hPutStr,hClose);
import Data.ByteString.Lazy (hPut,hGetContents,intercalate,ByteString);
import Data.ByteString.Lazy.Char8 (pack,unpack,uncons,cons);
import GHC.IO.Exception (ExitCode(ExitSuccess));
import Data.Char (isNumber, isSpace);
import GHC.IO.Handle (hSetBinaryMode,hSetBuffering,BufferMode(BlockBuffering));
import Control.Exception;
import Data.IORef;

fplll_command :: String;
fplll_command = "fplll";

default_eta :: Double;
default_eta = 0.51;

alpha_to_delta :: (Integer,Integer) -> Double;
alpha_to_delta (num,denom) = (fromIntegral denom / fromIntegral num) + 
  (default_eta * default_eta);

showrow :: [Integer] -> ByteString;
showrow rowA = (pack "[") `mappend` intercalate (pack " ") (map (pack . show) rowA) `mappend` (pack "]");
showmat :: [[Integer]] -> ByteString;
showmat matA = (pack "[") `mappend` intercalate (pack "\n ") (map showrow matA) `mappend` (pack "]");

data Mode = Simple | Certificate;

flags :: Mode -> String;
flags Simple = "b";
flags Certificate = "bvu";

getMode xs = (let m = length xs in if m == 0 then Certificate
  else if m == length (head xs) then Simple else Certificate);

fplll_solver :: (Integer,Integer) -> [[Integer]] -> ([[Integer]], Maybe ([[Integer]],[[Integer]]));
fplll_solver alpha in_mat = unsafePerformIO $ catchE $ do {
  (Just f_in,Just f_out,Just f_err,f_pid) <- createProcess (proc fplll_command ["-e", show default_eta, "-d", show (alpha_to_delta alpha), "-of", flags mode]){std_in = CreatePipe, std_err = CreatePipe, std_out = CreatePipe};
  hSetBinaryMode f_in True;
  hSetBinaryMode f_out True;
  hSetBinaryMode f_err True;
  hSetBuffering f_out (BlockBuffering Nothing);
  hPut f_in (showmat in_mat);
  res <- hGetContents f_out;
  hClose f_in;
  parseRes res}
 where {
   mode = getMode in_mat;
   catchE m = catch m def;
   def :: SomeException -> IO ([[Integer]], Maybe ([[Integer]], [[Integer]]));
   def _ = seq sendError $ default_answer;
   unconsIO a = case uncons a of{
      Just b -> return b;
      _ -> abort "Unexpected end of file / input"};
   parseMat ('[',as)
    = do {
      (h0,rem0) <- parseSpaces =<< unconsIO as;
      (rows,(h1,rem1)) <- parseRows (h0,rem0);
      case seq rows h1 of{
        ']' -> return (rows,rem1);
        _ -> abort$ "Expecting closing ']' while parsing a matrix.\n"}
      } :: IO ([[Integer]], ByteString);
   parseMat _ = abort "Expecting opening '[' while parsing a matrix";
   parseRows ('[',rem0)
    = do {
     (nums,(h2,rem2))<-parseNums =<< parseSpaces =<< unconsIO rem0;
     case seq nums h2 of
       ']' -> do { (h4,rem4) <- parseSpaces =<< unconsIO rem2;
                   (rows,rem5) <- parseRows (h4,rem4);
                   return (nums:rows,rem5) }
       _ -> abort$ "Expecting closing ']' while parsing a row\n"
       } :: IO ([[Integer]],(Char, ByteString));
   parseRows r = return ([],r);
   parseNums (a,rem0) =
     (if isNumber a || a == '-' then do {
       (n,(h1,rem1)) <- parseNum =<< unconsIO rem0;
       rem2 <- parseSpaces (h1,rem1);
       num <- return (read (a:n));
       (nums,rem3) <- seq (num==num)$ parseNums rem2;
       return (seq nums $ num:nums,rem3) }
     else if isSpace a then do {
       rem1 <- parseSpaces (a,rem0);
       parseNums rem1}
     else return ([],(a, rem0))) :: IO ([Integer], (Char, ByteString));
   parseNum (a,rem0) =
     if isNumber a then do {
       (num,rem1) <- parseNum =<< unconsIO rem0;
       return (a:num,rem1) 
       }
     else return (mempty,(a,rem0));
   parseSpaces (a,as) = if isSpace a then case uncons as of { Nothing -> return (a,mempty); Just v -> parseSpaces v } else return (a,as);
   parseRes :: ByteString -> IO ([[Integer]], Maybe ([[Integer]], [[Integer]]));
   parseRes res = if res == mempty
       then default_answer
       else do {
         rem0' <- parseSpaces =<< unconsIO res;
         (m1,rem1) <- parseMat rem0';
         -- putStrLn "Parsed a matrix";
         case mode of 
           Simple -> return (m1, Nothing);
           _ -> do {
             rem1' <- parseSpaces =<< unconsIO rem1;
             (m2,rem2) <- seq m1$ parseMat rem1';
             -- putStrLn "Parsed a matrix";
             rem2' <- parseSpaces =<< unconsIO rem2;
             (m3,rem3) <- seq m2$ parseMat rem2';
             seq m3$ return ();
             -- putStrLn "Parsed a matrix";
             if rem3 /= mempty
                then do { (_,rem2') <- parseSpaces =<< unconsIO rem3;
                          if rem2' /= mempty
                             then abort "Unexpected output after parsing three matrices."
                             else return (m1, Just (m2,m3)) }
                else return (m1,Just (m2,m3))
                }
        };
   fail_to_execute = seq sendError default_answer;
   
   default_answer = -- not small enough, but it'll be accepted
     return (in_mat, case mode of Simple -> Nothing; _ -> Just (id_ofsize (length in_mat),id_ofsize (length in_mat)));
   abort str = error$ "Runtime exception in parsing fplll output:\n"++str;
   };
   

sendError :: (); -- bad trick using unsafeIO to make this error only appear once. I believe this is OK since the error is non-critical and the 'only appear once' is non-critical too.
sendError = unsafePerformIO $ do {
  hPutStrLn stderr "--- WARNING ---";
  hPutStrLn stderr "Failed to run fplll.";
  hPutStrLn stderr "To remove this warning, either:";
  hPutStrLn stderr "  - install fplll and ensure it is in your path.";
  hPutStrLn stderr "  - create an executable fplll that always returns successfully without generating output.";
  hPutStrLn stderr "Installing fplll correctly helps to reduce time spent verifying your certificate.";
  hPutStrLn stderr "--- END OF WARNING ---"
  };

id_ofsize :: Int -> [[Integer]];
id_ofsize n = [[if i == j then 1 else 0 | j <- [0..n-1]] | i <- [0..n-1]];
}\<close>

code_reserved Haskell FPLLL_Solver fplll_solver

code_printing
  constant external_lll_solver \<rightharpoonup> (Haskell) "FPLLL'_Solver.fplll'_solver"
| constant enable_external_lll_solver \<rightharpoonup> (Haskell) "True"

text \<open>Note that since we only enabled the external LLL solver for Haskell, the result of 
  @{const short_vector_hybrid} will usually differ when executed in Haskell in
  comparison to any of the other target languages. For instance, consider the 
  invocation of:\<close>

value (code) "short_vector_test_hybrid [[1,4903,4902], [0,39023,0], [0,0,39023]]" 

text \<open>The above value-command evaluates the expression in Eval/SML to 77714 (by computing
  a short vector solely by the verified @{const short_vector} algorithm, whereas
  the generated Haskell-code via the external LLL solver yields 60414!\<close>

(* export_code short_vector_test_hybrid in Haskell module_name LLL *)
end
