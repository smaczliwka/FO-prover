{-# LANGUAGE UnicodeSyntax, TypeSynonymInstances, FlexibleInstances, LambdaCase #-}

module Main where

import Data.List

import System.IO
import System.Random
import System.Timeout

import Text.Printf

import Control.Monad.State

import Test.QuickCheck hiding (Fun, (===))

import Formula
import Parser hiding (one)

update :: Eq a => (a -> b) -> a -> b -> a -> b
update f a b x | x == a = b
               | otherwise = f x

variants :: VarName -> [VarName]
variants x = x : [x ++ show n | n <- [0..]]

varsT :: Term -> [VarName]
varsT (Var x) = [x]
varsT (Fun _ ts) = nub $ concatMap varsT ts

-----------------------------------------------------------

vars :: Formula -> [VarName]
vars T = []
vars F = []
vars (Rel _ ts) = varsT (Fun "dummy" ts)
vars (Not phi) = vars phi
vars (And phi psi) = nub $ vars phi ++ vars psi
vars (Or phi psi) = nub $ vars phi ++ vars psi
vars (Implies phi psi) = nub $ vars phi ++ vars psi
vars (Iff phi psi) = nub $ vars phi ++ vars psi
vars (Exists x phi) = nub $ x : vars phi
vars (Forall x phi) = nub $ x : vars phi

-----------------------------------------------------------

freshIn :: VarName -> Formula -> Bool
x `freshIn` phi = not $ x `elem` vars phi

-----------------------------------------------------------

freshVariant :: VarName -> Formula -> VarName
freshVariant x phi = head [ y | y <- variants x, y `freshIn` phi ]

-----------------------------------------------------------

-- fv :: Formula -> [VarName]
-- fv T = []
-- fv F = []
-- fv (Rel _ ts) = varsT (Fun "dummy" ts)
-- fv (Not phi) = fv phi
-- fv (And phi psi) = nub $ fv phi ++ fv psi
-- fv (Or phi psi) = nub $ fv phi ++ fv psi
-- fv (Implies phi psi) = nub $ fv phi ++ fv psi
-- fv (Iff phi psi) = nub $ fv phi ++ fv psi
-- fv (Exists x phi) = delete x $ fv phi
-- fv (Forall x phi) = delete x $ fv phi

-----------------------------------------------------------

renameT :: VarName -> VarName -> Term -> Term
renameT x y (Var z)
  | z == x = Var y
  | otherwise = Var z
renameT x y (Fun f ts) = Fun f (map (renameT x y) ts)

rename :: VarName -> VarName -> Formula -> Formula
rename x y T = T
rename x y F = F
rename x y (Rel r ts) = Rel r (map (renameT x y) ts)
rename x y (Not phi) = Not (rename x y phi)
rename x y (And phi psi) = And (rename x y phi) (rename x y psi)
rename x y (Or phi psi) = Or (rename x y phi) (rename x y psi)
rename x y (Implies phi psi) = Implies (rename x y phi) (rename x y psi)
rename x y (Iff phi psi) = Iff (rename x y phi) (rename x y psi)
rename x y (Forall z phi)
  | z == x = Forall z phi
  | otherwise = Forall z (rename x y phi)
rename x y (Exists z phi)
  | z == x = Exists z phi
  | otherwise = Exists z (rename x y phi)

-----------------------------------------------------------

-- type Substitution = VarName -> Term

substT :: Substitution -> Term -> Term
substT σ (Var x) = σ x
substT σ (Fun f ts) = Fun f (map (substT σ) ts)

subst :: Substitution -> Formula -> Formula
subst _ T = T
subst _ F = F
subst σ (Rel r ts) = Rel r $ map (substT σ) ts
subst σ (Not phi) = Not $ subst σ phi
subst σ (And phi psi) = And (subst σ phi) (subst σ psi)
subst σ (Or phi psi) = Or (subst σ phi) (subst σ psi)
subst σ (Implies phi psi) = Implies (subst σ phi) (subst σ psi)
subst σ (Iff phi psi) = Iff (subst σ phi) (subst σ psi)
subst σ (Exists x phi) = Exists x (subst (update σ x (Var x)) phi)
subst σ (Forall x phi) = Forall x (subst (update σ x (Var x)) phi)

-------------------------------------------------------------

generalise :: Formula -> Formula
generalise phi = go $ fv phi
  where go [] = phi
        go (x:xs) = Forall x $ go xs

------------------------------------------------------------

fresh :: Formula -> Formula
fresh phi = evalState (go phi) []
  where go :: Formula -> State [VarName] Formula
        go T = return T
        go F = return F
        go phi@(Rel _ _) = return phi
        go (Not phi) = liftM Not (go phi)
        go (And phi psi) = liftM2 And (go phi) (go psi)
        go (Or phi psi) = liftM2 Or (go phi) (go psi)
        go (Implies phi psi) = liftM2 Implies (go phi) (go psi)
        go (Iff phi psi) = liftM2 Iff (go phi) (go psi)
        go (Forall x phi) = go2 Forall x phi
        go (Exists x phi) = go2 Exists x phi

        go2 quantifier x phi =
          do xs <- get
             let y = head [y | y <- variants x, not $ y `elem` xs]
             let psi = rename x y phi
             put $ y : xs
             liftM (quantifier y) $ go psi

-------------------------------------------------------------

nnf :: Formula -> Formula
nnf T = T
nnf F = F
nnf (Rel relName terms) = Rel relName terms
nnf (And phi psi) = And (nnf phi) (nnf psi)
nnf (Or phi psi) = Or (nnf phi) (nnf psi)
nnf (Implies phi psi) = Or (nnf (Not phi)) (nnf psi)
nnf (Iff phi psi) = And (nnf (Implies phi psi)) (nnf (Implies psi phi))
nnf (Exists x phi) = Exists x (nnf phi)
nnf (Forall x phi) = Forall x (nnf phi)

nnf (Not T) = F
nnf (Not F) = T
nnf (Not (Rel relName terms)) = Not (Rel relName terms)
nnf (Not (Not phi)) = nnf phi
nnf (Not (And phi psi)) = Or (nnf (Not phi)) (nnf (Not psi))
nnf (Not (Or phi psi)) = And (nnf (Not phi)) (nnf (Not psi))
nnf (Not (Implies phi psi)) = nnf (Not (nnf (Implies phi psi)))
nnf (Not (Iff phi psi)) = nnf (Not (nnf (Iff phi psi)))
nnf (Not (Exists x phi)) = Forall x (nnf (Not phi))
nnf (Not (Forall x phi)) = Exists x (nnf (Not phi))

------------------------------------------------------------

-- prenex normal form (all quantifiers in front)
pnf :: Formula -> Formula
pnf phi = pnfHelper (nnf phi)

pnfHelper :: Formula -> Formula
pnfHelper T = T
pnfHelper F = F
pnfHelper (Rel relName terms) = Rel relName terms
pnfHelper (Not (Rel relName terms)) = Not (Rel relName terms)

pnfHelper (And phi psi) =
  let phi' = pnfHelper phi in
    let psi' = pnfHelper psi in
      reduce (And phi' psi')

pnfHelper (Or phi psi) =
  let phi' = pnfHelper phi in
    let psi' = pnfHelper psi in
      reduce (Or phi' psi')

pnfHelper (Implies phi psi) = error "not an NNF formula"
pnfHelper (Iff phi psi) = error "not an NNF formula"
pnfHelper (Not _) = error "not an NNF formula"
pnfHelper (Exists x phi) = Exists x (pnf phi)
pnfHelper (Forall x phi) = Forall x (pnf phi)

reduce :: Formula -> Formula

reduce (And (Forall x phi) psi) =
    let x' = freshVariant x (And phi psi) in
      Forall x' (reduce (And (rename x x' phi) psi))
reduce (And (Exists x phi) psi) =
  let x' = freshVariant x (And phi psi) in
    Exists x' (reduce (And (rename x x' phi) psi))
reduce (And phi (Forall x psi)) =
  let x' = freshVariant x (And phi psi) in
    Forall x' (reduce (And phi (rename x x' psi)))
reduce (And phi (Exists x psi)) =
  let x' = freshVariant x (And phi psi) in
    Exists x' (reduce (And phi (rename x x' psi)))

reduce (Or (Forall x phi) psi) =
  let x' = freshVariant x (Or phi psi) in
    Forall x' (reduce (Or (rename x x' phi) psi))
reduce (Or (Exists x phi) psi) =
  let x' = freshVariant x (Or phi psi) in
    Exists x' (reduce (Or (rename x x' phi) psi))
reduce (Or phi (Forall x psi)) =
  let x' = freshVariant x (Or phi psi) in
    Forall x' (reduce (Or phi (rename x x' psi)))
reduce (Or phi (Exists x psi)) =
  let x' = freshVariant x (Or phi psi) in
    Exists x' (reduce (Or phi (rename x x' psi)))

reduce (And phi psi) = And phi psi
reduce (Or phi psi) = Or phi psi

--------------------------------------------------------------

skolemise :: Formula -> Formula
skolemise phi = pnf (skolemFunction [] f (fresh (nnf (close phi)))) where
  f x = Var x

close :: Formula -> Formula
close phi = go $ fv phi
  where go [] = phi
        go (x:xs) = Exists x $ go xs

skolemFunction :: [Term] -> Substitution -> Formula -> Formula
skolemFunction univar repl T  = T
skolemFunction univar repl F = F
skolemFunction univar repl (Rel relName terms) = Rel relName (map (substT repl) terms)
skolemFunction univar repl (Not phi) = Not (skolemFunction univar repl phi)
skolemFunction univar repl (And phi psi) =
  And (skolemFunction univar repl phi) (skolemFunction univar repl psi)
skolemFunction univar repl (Or phi psi) =
  Or (skolemFunction univar repl phi) (skolemFunction univar repl psi)
skolemFunction univar repl (Implies phi psi) =
  Implies (skolemFunction univar repl phi) (skolemFunction univar repl psi)
skolemFunction univar repl (Iff phi psi) =
  Iff (skolemFunction univar repl phi) (skolemFunction univar repl psi)
skolemFunction univar repl (Exists y phi) = let repl' = update repl y (Fun y univar) in
  skolemFunction univar repl' phi
skolemFunction univar repl (Forall x phi) = let univar' = ((Var x) : univar) in
  Forall x (skolemFunction univar' repl phi)

---------------------------------------------------------------

-- Wszystkie sygnatury funkcji występujące w termie

funsT :: Term -> [(FunName, Int)]
funsT (Var x) = []
funsT (Fun fname ts) = nub $ (fname, length ts) : concatMap funsT ts

-- Wszystkie sygnatury funkcji występujące w formule

funs :: Formula -> [(FunName, Int)]
funs T = []
funs F = []
funs (Rel _ ts) = nub $ concatMap funsT ts
funs (Not phi) = funs phi
funs (And phi psi) = nub $ funs phi ++ funs psi
funs (Or phi psi) = nub $ funs phi ++ funs psi
funs (Implies phi psi) = nub $ funs phi ++ funs psi
funs (Iff phi psi) = nub $ funs phi ++ funs psi
funs (Exists x phi) = funs phi
funs (Forall x phi) = funs phi

isConst :: (FunName, Int) -> Bool
isConst (_, nargs) = nargs == 0

-- argList :: (FunName, Int) -> (FunName, [Int])
-- argList (fname, n) = (fname, [1..n])

noArgFun :: FunName -> Term
noArgFun fname = Fun fname []

-- argFun :: [Term] -> [(FunName)]

-- countArgs :: Int -> [(FunName, [Int])] -> [(FunName, Int)] -> ([Int], [(FunName, [Int])])
-- countArgs first acc [] = ([0..first - 1], reverse acc)
-- countArgs first acc ((fname, nargs) : rest) =
--   countArgs (first + nargs) ((fname, [first..first+nargs-1]) : acc) rest

-- alternating merge of two (potentially infinite) lists
merge :: [a] -> [a] -> [a]
merge [] bs = bs
merge (a : as) bs = a : merge bs as

-- alternating merge of a (potentially infinite) list of (potentially infinite) lists
merges :: [[a]] -> [a]
merges [] = []
merges (as:ass) = merge as (merges ass)

-- collect all functions from a finite list to a (potentially infinite) list
functions :: Eq a => [a] -> [b] -> [a -> b]
functions [] _ = [undefined]
functions (a:as) bs = merges [[update f a b | f <- functions as bs] | b <- bs]

herbrandtUniverse :: Formula -> [Term]

-- herbrandtUniverse phi = []

herbrandtUniverse phi =
  let (c, f) = partition isConst (funs phi) in
    let c' = if null c then [noArgFun "c"] else map (noArgFun . fst) c in
      -- let (allArgs, f') = countArgs 0 [] f in
        let universe = c' ++ merges [[Fun fname (map subst [1..nargs]) | subst <- functions [1..nargs] universe] | (fname, nargs) <- f] in
        -- let universe = c' ++ [Fun fname (map subst args) | (fname, args) <- f', subst <- functions args c'] in
          universe


quantifierFree :: Formula -> Formula
quantifierFree phi = case phi of
  Forall _ psi -> quantifierFree psi
  psi -> psi

groundInstances :: Formula -> [Term] -> [Formula]
groundInstances phi ts =
  let fvs = fv phi in
    let repls = functions fvs ts in
      map f repls where
        f repl = subst repl phi

-- TODO: use Davis-Putnam
atomicFormulas :: Formula -> [Formula]
atomicFormulas T = []
atomicFormulas F = []
atomicFormulas phi@(Rel _ ts) = [phi]
atomicFormulas (Not phi) = atomicFormulas phi
atomicFormulas (And phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Or phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Implies phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Iff phi psi) = nub $ atomicFormulas phi ++ atomicFormulas psi
atomicFormulas (Exists x phi) = atomicFormulas phi
atomicFormulas (Forall x phi) = atomicFormulas phi

sat :: Formula -> Bool
sat phi = or [ev int phi | int <- functions atoms [True, False]]
  where atoms = atomicFormulas phi
        ev :: (Formula -> Bool) -> Formula -> Bool
        ev int T = True
        ev int F = False
        ev int atom@(Rel _ _) = int atom
        ev int (Not φ) = not (ev int φ)
        ev int (Or φ ψ) = ev int φ || ev int ψ
        ev int (And φ ψ) = ev int φ && ev int ψ
        ev _ φ = error $ "unexpected formula: " ++ show φ

-- Sprawdza kolejne prefiksy aż znajdzie niespełnialny
check :: Formula -> [Formula] -> Bool
check phi forms =
  sat phi && (case forms of
    [] -> True
    (psi : rest) -> check (And phi psi) rest)


prover :: Formula -> Bool
prover phi =
  let psi = skolemise (Not phi) in
    let ksi = quantifierFree psi in
      let universe = herbrandtUniverse ksi in
        let instances = groundInstances ksi universe in
          not (check T instances)


main :: IO ()
main = do
    eof <- hIsEOF stdin
    if eof
        then return ()
        else do
                line <- getLine -- read the input
                let phi = parseString line -- call the parser
                let res = prover phi -- call the prover
                if res
                  then putStrLn "1" -- write 1 if the formula is a tautology
                  else putStrLn "0" -- write 0 if the formula is not a tautology