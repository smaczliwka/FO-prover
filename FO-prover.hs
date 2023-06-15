{-# LANGUAGE UnicodeSyntax, FlexibleInstances #-}

module Main where

import Data.List ( map, (\\), intersect, partition, nub)
import Data.Map(Map, member, insert, size, empty, (!))

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

--------------------------------------------------------------

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

--------------------------------------------------------------

freshIn :: VarName -> Formula -> Bool
x `freshIn` phi = x `notElem` vars phi

--------------------------------------------------------------

freshVariant :: VarName -> Formula -> VarName
freshVariant x phi = head [ y | y <- variants x, y `freshIn` phi ]

--------------------------------------------------------------

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

--------------------------------------------------------------

substT :: Substitution -> Term -> Term
substT rho (Var x) = rho x
substT rho (Fun f ts) = Fun f (map (substT rho) ts)

subst :: Substitution -> Formula -> Formula
subst _ T = T
subst _ F = F
subst rho (Rel r ts) = Rel r $ map (substT rho) ts
subst rho (Not phi) = Not $ subst rho phi
subst rho (And phi psi) = And (subst rho phi) (subst rho psi)
subst rho (Or phi psi) = Or (subst rho phi) (subst rho psi)
subst rho (Implies phi psi) = Implies (subst rho phi) (subst rho psi)
subst rho (Iff phi psi) = Iff (subst rho phi) (subst rho psi)
subst rho (Exists x phi) = Exists x (subst (update rho x (Var x)) phi)
subst rho (Forall x phi) = Forall x (subst (update rho x (Var x)) phi)

--------------------------------------------------------------

generalise :: Formula -> Formula
generalise phi = go $ fv phi
  where go [] = phi
        go (x:xs) = Forall x $ go xs

--------------------------------------------------------------

fresh :: Formula -> Formula
fresh phi = evalState (go phi) []
  where go :: Formula -> State [VarName] Formula
        go T = return T
        go F = return F
        go phi@(Rel _ _) = return phi
        go (Not phi) = fmap Not (go phi)
        go (And phi psi) = liftM2 And (go phi) (go psi)
        go (Or phi psi) = liftM2 Or (go phi) (go psi)
        go (Implies phi psi) = liftM2 Implies (go phi) (go psi)
        go (Iff phi psi) = liftM2 Iff (go phi) (go psi)
        go (Forall x phi) = go2 Forall x phi
        go (Exists x phi) = go2 Exists x phi

        go2 quantifier x phi =
          do xs <- get
             let y = head [y | y <- variants x, y `notElem` xs]
             let psi = rename x y phi
             put $ y : xs
             quantifier y <$> go psi

--------------------------------------------------------------

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

--------------------------------------------------------------

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
  f = Var

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
skolemFunction univar repl (Forall x phi) = let univar' = (Var x : univar) in
  Forall x (skolemFunction univar' repl phi)

--------------------------------------------------------------

sigT :: Term -> [(FunName, Int)]
sigT (Var x) = []
sigT (Fun fname ts) = nub $ (fname, length ts) : concatMap sigT ts

sig :: Formula -> [(FunName, Int)]
sig T = []
sig F = []
sig (Rel _ ts) = nub $ concatMap sigT ts
sig (Not phi) = sig phi
sig (And phi psi) = nub $ sig phi ++ sig psi
sig (Or phi psi) = nub $ sig phi ++ sig psi
sig (Implies phi psi) = nub $ sig phi ++ sig psi
sig (Iff phi psi) = nub $ sig phi ++ sig psi
sig (Exists x phi) = sig phi
sig (Forall x phi) = sig phi

--------------------------------------------------------------

-- Herbrandt universe generation

isConst :: (FunName, Int) -> Bool
isConst (_, nargs) = nargs == 0

noArgFun :: FunName -> Term
noArgFun fname = Fun fname []

-- alternating merge of two (potentially infinite) lists
merge :: [a] -> [a] -> [a]
merge [] bs = bs
merge (a : as) bs = a : merge bs as

-- alternating merge of a (potentially infinite) list of (potentially infinite) lists
merges :: [[a]] -> [a]
merges = foldr merge []

-- collect all functions from a finite list to a (potentially infinite) list
functions :: Eq a => [a] -> [b] -> [a -> b]
functions [] _ = [undefined]
functions (a:as) bs = merges [[update f a b | f <- functions as bs] | b <- bs]

herbrandt :: Formula -> [Term]

herbrandt phi =
  let (c, f) = partition isConst (sig phi) in
    let c' = if null c then [noArgFun "c"] else map (noArgFun . fst) c in
        let universe = c' ++ merges [[Fun fname (map subst [1..nargs]) | subst <- functions [1..nargs] universe] | (fname, nargs) <- f] in
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

--------------------------------------------------------------

-- Davis-Putnam SAT solver

type PropName = Int

data Literal = Pos PropName | Neg PropName deriving (Eq, Show, Ord)

literal2var :: Literal -> PropName
literal2var (Pos p) = p
literal2var (Neg p) = p

opposite :: Literal -> Literal
opposite (Pos p) = Neg p
opposite (Neg p) = Pos p

type CNFClause = [Literal]
type CNF = [CNFClause]

positiveLiterals :: CNFClause -> [PropName]
positiveLiterals ls = nub [p | Pos p <- ls]

negativeLiterals :: CNFClause -> [PropName]
negativeLiterals ls = nub [p | Neg p <- ls]

removeTautologies :: CNF -> CNF
removeTautologies = filter notTautological

notTautological :: CNFClause -> Bool
notTautological clause =
  null (positive `intersect` negative)
  where
    positive = positiveLiterals clause
    negative = negativeLiterals clause

oneLiteral :: CNF -> CNF
oneLiteral cnf = case toRemove cnf of
  Nothing -> cnf
  Just literal ->
    let cnf' = map (removeOpposites literal) cnf in
      let cnf'' = filter (notContaining literal) cnf' in
        oneLiteral cnf''

toRemove :: CNF -> Maybe Literal
toRemove [] = Nothing
toRemove (clause : rest) =
  case nub clause of
    [l] -> Just l
    _ -> toRemove rest

removeOpposites :: Literal -> CNFClause -> CNFClause
removeOpposites literal = filter (/=opposite literal)

notContaining :: Literal -> CNFClause -> Bool
notContaining = notElem

affirmativeNegative :: CNF -> CNF
affirmativeNegative cnf =
  filter (allInList (both cnf)) cnf

both :: CNF -> [PropName]
both cnf =
  let positive = concatMap positiveLiterals cnf in
    let negative = concatMap negativeLiterals cnf in
      intersect positive negative

allInList :: [PropName] -> CNFClause -> Bool
allInList list clause =
  let vars = map literal2var clause in
    null (vars \\ list)

resolution :: CNF -> CNF
resolution cnf = case getVar cnf of
  Nothing -> cnf
  Just var -> let (positive, negative, rest) = splitClauses var cnf in
    prod positive negative ++ rest

getVar :: CNF -> Maybe PropName
getVar cnf = case cnf of
  [] -> Nothing
  ([] : rest) -> getVar rest
  ((literal : _) : _) -> Just (literal2var literal)

prod :: [[a]] -> [[a]] -> [[a]]
prod = liftM2 (++)

splitClauses :: PropName -> CNF -> (CNF, CNF, CNF)
splitClauses var cnf =
  let positive = filter (elem (Pos var)) cnf in
    let negative = filter (elem (Neg var)) cnf in
      let rest = (cnf \\ positive) \\ negative in
        (map (filter (/= Pos var)) positive, map (filter (/= Neg var)) negative, rest)

dp :: CNF -> Bool
dp cnf
  | null cnf = True
  | [] `elem` cnf = False
  | otherwise = let cnf' = affirmativeNegative (oneLiteral (removeTautologies cnf)) in
    case getVar cnf' of
      Nothing -> dp cnf'
      Just var -> dp ([Pos var] : cnf') || dp ([Neg var] : cnf')
    -- dp (resolution cnf')

relVariables :: Map (RelName, [Term]) PropName -> Formula -> Map (RelName, [Term]) PropName
relVariables acc phi = case phi of
  F -> acc
  T -> acc
  Rel relName terms ->
    if member (relName, terms) acc then acc
    else insert (relName, terms) (size acc) acc
  Not psi -> relVariables acc psi
  And psi1 psi2 ->
    let vars1 = relVariables acc psi1 in
      relVariables vars1 psi2
  Or psi1 psi2 ->
    let vars1 = relVariables acc psi1 in
      relVariables vars1 psi2
  Implies psi1 psi2 ->
    let vars1 = relVariables acc psi1 in
      relVariables vars1 psi2
  Iff psi1 psi2 ->
    let vars1 = relVariables acc psi1 in
      relVariables vars1 psi2
  Exists _ psi -> relVariables acc psi
  Forall _ psi -> relVariables acc psi

ecnf :: Formula -> CNF

ecnf f =
  let vars = relVariables empty f in
    let p = size vars in
      let (cnf, literal, _) = ecnfHelper f (p + 1) vars p in
        ([Pos p] : [literal] : cnf)

ecnfHelper :: Formula -> PropName -> Map (RelName, [Term]) PropName -> PropName -> (CNF, Literal, PropName)
ecnfHelper f next variables p = case f of
  T -> ([], Pos p, next)
  F -> ([], Neg p, next)
  Rel relName terms -> ([], Pos (variables ! (relName, terms)), next)
  Not f1 ->
    let (cnf1, a, next1) = ecnfHelper f1 next variables p in
      (cnf1, opposite a, next1)
  And f1 f2 ->
    let (cnf1, a, next1) = ecnfHelper f1 next variables p in
      let (cnf2, b, next2) = ecnfHelper f2 next1 variables p in
        let var = next2 in
          (cnf1 ++ cnf2 ++ [[opposite a, opposite b, Pos var], [a, Neg var], [b, Neg var]],
          Pos var,
          next2 + 1)
  Or f1 f2 ->
    let (cnf1, a, next1) = ecnfHelper f1 next variables p in
      let (cnf2, b, next2) = ecnfHelper f2 next1 variables p in
        let var = next2 in
          (cnf1 ++ cnf2 ++ [[opposite a, Pos var], [a, b, Neg var], [opposite b, Pos var]],
          Pos var,
          next2 + 1)
  Implies f1 f2 ->
    let (cnf1, a, next1) = ecnfHelper f1 next variables p in
      let (cnf2, b, next2) = ecnfHelper f2 next1 variables p in
        let var = next2 in
          (cnf1 ++ cnf2 ++ [[Neg var, opposite a, b], [a, Pos var], [opposite b, Pos var]],
          Pos var,
          next2 + 1)
  Iff f1 f2 ->
    let (cnf1, a, next1) = ecnfHelper f1 next variables p in
      let (cnf2, b, next2) = ecnfHelper f2 next1 variables p in
        let var = next2 in
          (cnf1 ++ cnf2 ++ [[Neg var, opposite a, b], [Neg var, opposite b, a], [a, b, Pos var],
          [a, opposite a, Pos var], [opposite b, b, Pos var], [opposite b, opposite a, Pos var]],
          Pos var,
          next2 + 1)

--------------------------------------------------------------

-- Optimization for trivial formulas

data Trivial = Tautology | NotTautology | AntiTautology

trivial :: Formula -> Maybe Trivial
trivial phi = case phi of
  F -> Just AntiTautology
  T -> Just Tautology
  Rel relName terms -> Just NotTautology
  Not psi -> case trivial psi of
    Nothing -> Nothing
    Just Tautology -> Just AntiTautology
    Just AntiTautology -> Just Tautology
    Just NotTautology -> Just NotTautology
  Exists _ psi -> trivial psi
  Forall _ psi -> trivial psi
  And psi1 psi2 -> case (trivial psi1, trivial psi2) of
    (Just Tautology, Just Tautology) -> Just Tautology
    (Just AntiTautology, _) -> Just AntiTautology
    (_, Just AntiTautology) -> Just AntiTautology
    _ -> Nothing
  Or psi1 psi2 -> case (trivial psi1, trivial psi2) of
    (Just AntiTautology, Just AntiTautology) -> Just AntiTautology
    (Just Tautology, _) -> Just Tautology
    (_, Just Tautology) -> Just Tautology
    _ -> Nothing
  Implies psi1 psi2 -> trivial (Or (Not psi1) psi2)
  Iff psi1 psi2 -> trivial (And (Implies psi1 psi2) (Implies psi2 psi1))

--------------------------------------------------------------

sat :: Formula -> Bool
sat phi = dp (ecnf phi)

-- check conjunctions of prefixes unfil unsatisfiable is found
check :: Formula -> [Formula] -> Bool
check phi forms =
  sat phi && (case forms of
    [] -> True
    (psi : rest) -> check (And phi psi) rest)

prover :: Formula -> Bool
prover phi =
  case trivial phi of
    Just Tautology -> True
    Just AntiTautology -> False
    Just NotTautology -> False
    Nothing ->
      let psi = skolemise (Not phi) in
        let ksi = quantifierFree psi in
          let universe = herbrandt ksi in
            let instances = groundInstances ksi universe in
              not (check T instances)

main :: IO ()
main = do
    eof <- isEOF
    if eof
        then return ()
        else do
                line <- getLine -- read the input
                let phi = parseString line -- call the parser
                let res = prover phi -- call the prover
                if res
                  then putStrLn "1" -- write 1 if the formula is a tautology
                  else putStrLn "0" -- write 0 if the formula is not a tautology
