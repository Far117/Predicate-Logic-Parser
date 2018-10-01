
{-# OPTIONS_GHC -Wall #-}

import Data.Set        (toList, fromList)
import Data.Char       (isAlpha)
import Numeric.Natural (Natural)


{--

Grammar for Predicate Logic:

Variable:
  [a-z]+

Binary Operator:
  ||
  &&
  ->
  <->

Unary Operator:
  !

Statement:
  <Variable>
  <Unary Operator> (<Statement>)
  (<Statement>) <Binary Operator> (<Statement>)

--}

data UnaryOperator = NOT
  deriving (Show)

data BinaryOperator = AND
                    | NAND
                    | OR
                    | XOR
                    | Implies
                    | Biconditional
                    deriving (Show)

data Token = TokVariable Char
           | TokUnary UnaryOperator
           | TokBinary BinaryOperator
           | TokComplex [Token]
           deriving (Show)

data Statement = Variable Char
               | Literal Bool
               | UnaryStatement UnaryOperator Statement
               | BinaryStatement Statement BinaryOperator Statement
               | NullStatement
               deriving (Show)

{-|

Takes a string and steps through it chunk-by-chunk,
parsing it into a list of Tokens.

--}
tokenize :: String -> [Token]
tokenize []       = []
tokenize (' ':cs) = tokenize cs
tokenize (a:b:c:ds)
  | (a:b:c:[] == "<->") = TokBinary Biconditional : tokenize ds
tokenize (a:b:cs)
  | (a:b:[] == "&&") = TokBinary AND : tokenize cs
  | (a:b:[] == "||") = TokBinary OR : tokenize cs
  | (a:b:[] == "->") = TokBinary Implies : tokenize cs
  | (a:b:[] == "!(") = TokUnary NOT : (TokComplex (tokenize cs)) : tokenize (dropParen 0 cs)
  | (a == '!')       = TokComplex (TokUnary NOT : tokenize [b]) : tokenize cs
tokenize (c:cs)
  | (c == '|')  = TokBinary XOR : tokenize cs
  | (c == '&')  = TokBinary NAND : tokenize cs
  | (c == '(')  = TokComplex (tokenize cs) : tokenize (dropParen 0 cs)
  | (c == ')')  = []
  | (c == '!')  = [TokComplex (TokUnary NOT : tokenize cs)]
  | (isAlpha c) = TokVariable c : tokenize cs
tokenize _ = error "Malformed input"

-- | Given a string starting with a '(', removes all characters up to and including its ')'.
dropParen :: Natural -> String -> String
dropParen _ []       = error "Malformed input"
dropParen n ('(':ss) = dropParen (succ n) ss
dropParen 0 (')':ss) = ss
dropParen n (')':ss) = dropParen (pred n) ss
dropParen n (_:ss)   = dropParen n ss

{-|

Finalizes the transformation of a list of Tokens into a fully-parsed Statement.
Transforming some string `s` into a statement would thus take the form of:

parse $ tokenize s

--}
parse :: [Token] -> Statement
parse []         = NullStatement                                                                                  
parse (TokUnary u : TokComplex c : TokBinary b : rest) = let left = UnaryStatement u (parse c) in
                                                           let right = parse rest in
                                                             BinaryStatement left b right
parse (TokComplex l : TokBinary b : rest)              = BinaryStatement (parse l) b (parse rest)
parse (TokVariable l : TokBinary b : rest)             = BinaryStatement (Variable l) b (parse rest)
parse (TokUnary u : TokComplex c : [])                 = UnaryStatement u (parse c)
parse (TokUnary u : TokVariable v : [])                = UnaryStatement u (Variable v)
parse (TokComplex c : [])                              = parse c
parse (TokVariable v : [])                             = Variable v
parse _                                                = error "Malformed input"

-- | Given a Statement with no Variables, checks if it's True or False.
evaluate :: Statement -> Bool
evaluate NullStatement           = error "Cannot evaluate a null statement"
evaluate (Variable _)            = error "Cannot evaluate variable"
evaluate (Literal b)             = b
evaluate (UnaryStatement o s)    = case o of
                                     NOT -> not $ evaluate s
evaluate (BinaryStatement l o r) = case o of
                                     AND           -> (evaluate l) && (evaluate r)
                                     NAND          -> not $ (evaluate l) && (evaluate r)
                                     OR            -> (evaluate l) || (evaluate r)
                                     XOR           -> let left = evaluate l in
                                                        let right = evaluate r in
                                                          (left || right) && (not (left && right))
                                     Implies       -> if (evaluate l && (not (evaluate r))) then
                                                  False else True
                                     Biconditional -> (evaluate l) == (evaluate r)

-- | Replaces all instances of some Character Variable in a Statement with a boolean Literal.
inject :: Bool -> Char -> Statement -> Statement
inject b c (Variable v)            = if (c == v) then (Literal b) else (Variable v)
inject b c (UnaryStatement o s)    = let path = inject b c s in
                                       UnaryStatement o path
inject b c (BinaryStatement l o r) = let left = inject b c l in
                                       let right = inject b c r in
                                         BinaryStatement left o right
inject _ _ s                       = s

-- | Replaces all Variables with boolean Literals. The [Bool] and String must have the same length.
injectAll :: [Bool] -> String -> Statement -> Statement
injectAll bs vs st = let inputs = zip bs vs in
                      foldl (\s (b,v) -> inject b v s) st inputs

-- | Returns a String containing all unique Variables in a Statement
getVars :: Statement -> String
getVars st = toList . fromList $ loop st where
  loop (Variable p)            = [p]
  loop (UnaryStatement _ s)    = loop s
  loop (BinaryStatement l _ r) = (loop l) ++ (loop r)
  loop _                       = []

-- | Returns all possible combinations of True/False for a given number of Variables.
getValues :: Int -> [[Bool]]
getValues n = sequence (take n (repeat [False, True]))

{-|

Given a Statement:
  - Finds all variables in the Statement (see `let vars...`).
  - Calculates all possible inputs for its variables (see `let values...`).
  - Evaluates the function with each of these sets of inputs.
  - Zips the inputs with the evaluated results.

--}
calculateAll :: Statement -> [([Bool], Bool)]
calculateAll s = let vars = getVars s in
                   let values = getValues (length vars) in
                     let results = map (\v -> evaluate (injectAll v vars s)) values in
                       zip values results

-- | Displays the truth table of a Statement
printTruthTable :: Statement -> IO ()
printTruthTable s = do
  let vars    = getVars s
  let results = calculateAll s

  mapM_ (\c -> putStr (c : "\t"))  vars
  putStrLn "| Result"

  let printRow r = do
        mapM_ (\v -> putStr ((show v) ++ "\t")) (fst r)
        putStrLn ("| " ++ (show (snd r)))

  mapM_ (\r -> printRow r) results

-- | Convenience function for going from a String directly to a printed truth table
table :: String -> IO ()
table s = printTruthTable . parse $ tokenize s
