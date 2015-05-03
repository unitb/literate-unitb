{-# LANGUAGE DeriveGeneric        #-}
{-# LANGUAGE FlexibleInstances    #-}
{-# LANGUAGE TypeSynonymInstances #-}
{-# LANGUAGE TemplateHaskell      #-}
module Logic.Proof.Sequent where

    -- Modules
import Logic.Expr

    -- Libraries
import Control.DeepSeq

import Data.Char
import Data.DeriveTH
import Data.List as L
import Data.List.Ordered as OL hiding (merge)
import Data.Map  as M hiding ( map )
import Data.Maybe as MM
import qualified Data.Set  as S

import GHC.Generics

import Utilities.Format

type Sequent = AbsSequent GenericType HOQuantifier

type Sequent' = AbsSequent GenericType FOQuantifier

type FOSequent = AbsSequent FOType FOQuantifier

data AbsSequent t q = Sequent (AbsContext t q) [AbsExpr t q] (Map Label (AbsExpr t q)) (AbsExpr t q)
    deriving (Eq, Generic)

empty_sequent :: TypeSystem2 t => AbsSequent t q
empty_sequent = (Sequent empty_ctx [] M.empty ztrue)

instance (TypeSystem t, IsQuantifier q) => Show (AbsSequent t q) where
    show (Sequent (Context ss vs fs ds _) _ hs g) =
            unlines (
                   map (" " ++)
                (  ["sort: " ++ intercalate ", " (map f $ toList ss)]
                ++ (map show $ elems fs)
                ++ (map show $ elems ds)
                ++ (map show $ elems vs)
                ++ map pretty_print' (elems hs))
                ++ ["|----"," " ++ pretty_print' g] )
        where
            f (_, IntSort) = ""
            f (_, BoolSort) = ""
            f (_, RealSort) = ""
            f (x, Datatype args n _) = f (x, Sort n n $ length args)
            f (x, DefSort y z xs _)  = f (x, Sort y z $ length xs)
            f (_, Sort _ z 0) = z
            f (_, Sort _ z n) = format "{0} [{1}]" z (intersperse ',' $ map chr $ take n [ord 'a' ..]) 

remove_type_vars :: Sequent' -> FOSequent
remove_type_vars (Sequent ctx asm hyp goal) = Sequent ctx' asm' hyp' goal'
    where
        (Context sorts _ _ dd _) = ctx
        _ = dd :: Map String Def'
        asm_types = MM.catMaybes 
                    $ map type_strip_generics 
                    $ S.elems $ S.unions 
                    $ map used_types $ map target (M.elems dd) ++ asm ++ M.elems hyp
        seq_types = S.fromList asm_types `S.union` used_types goal'
        -- seq_types = S.unions $ L.map referenced_types $ asm_types ++ S.toList (used_types goal')

        decl_types :: S.Set FOType
        decl_types = S.unions $ map used_types $ goal' : asm' ++ M.elems hyp'
        
        ctx' :: FOContext
        ctx'  = to_fol_ctx decl_types ctx
        asm' :: [FOExpr]
        asm' = map snd $ concatMap (gen_to_fol seq_types (label "")) asm
        hyp' :: Map Label FOExpr
        hyp' = M.fromList $ concat $ M.elems $ M.mapWithKey (gen_to_fol seq_types) hyp
        goal' :: FOExpr
        goal' = vars_to_sorts sorts goal

one_point :: (IsQuantifier q, TypeSystem2 t) => AbsSequent t q -> AbsSequent t q
one_point (Sequent a b c g) = Sequent a asm c g'
    where
        asm
            | g == g'   = b
            | otherwise = b ++ [znot g]
        g' = one_point_rule g

differs_by_one :: Eq a => [a] -> [a] -> Maybe (Int,a,a)
differs_by_one xs ys = f $ zip [0..] $ zip xs ys
    where
        f [] = Nothing
        f ((i,(x,y)):xs) 
            | x == y        = f xs
            | all (uncurry (==) . snd) xs = Just (i,x,y)
            | otherwise     = Nothing

apply_monotonicity :: Sequent -> Sequent
apply_monotonicity po@(Sequent ctx asm h g) = maybe po id $
        let 
            h' = h
--            h' = M.insert (label $ fresh "~goal" $ S.map show $ keysSet h) (znot g) h 
            asm' = asm ++ [znot g]
            --asm' = znot g : asm
        in
        case g of
            Binder Forall (Var nam t:vs) rs ts _ -> do
                let (Context ss vars funs defs dums) = ctx
                    v   = Var (fresh nam $ 
                                      M.keysSet vars 
                            `S.union` M.keysSet funs
                            `S.union` M.keysSet defs) t
                    g'
                        | L.null vs = rs `zimplies` ts
                        | otherwise = zforall vs rs ts
                    ctx' = Context ss (M.insert (name v) v vars) funs defs dums
                return $ apply_monotonicity $ Sequent ctx' asm' h' 
                    (rename nam (name v) g')
            FunApp f [lhs, rhs] ->
                case (lhs,rhs) of
                    (Binder Forall vs r0 t0 _, Binder Forall us r1 t1 _) 
                        | shared vs us && name f `elem` ["=","=>"] -> do
                            let vs0 = vs L.\\ us
                                vs1 = us L.\\ vs
                                vs' = L.intersect vs us
                            return $ apply_monotonicity (Sequent ctx asm' h' 
                                (zforall vs' ztrue $ 
                                    FunApp f [zforall vs0 r0 t0, zforall vs1 r1 t1]))
                    (Binder Exists vs r0 t0 _, Binder Exists us r1 t1 _) 
                        | shared vs us && name f `elem` ["=","=>"] -> do
                            let vs0 = vs L.\\ us
                                vs1 = us L.\\ vs
                                vs' = L.intersect vs us
                            return $ apply_monotonicity (Sequent ctx asm' h' 
                                (zforall vs' ztrue $ 
                                    FunApp f [zexists vs0 r0 t0, zexists vs1 r1 t1]))
                    (Binder q0 vs r0 t0 _, Binder q1 us r1 t1 _)
                        | q0 == q1 && vs == us 
                            && r0 == r1 && name f == "=" -> 
                                return $ apply_monotonicity (Sequent ctx asm' h'
                                    (zforall vs r0 $ t0 `zeq` t1))
                        | q0 == q1 && vs == us 
                            && t0 == t1 && name f == "=" -> 
                                return $ apply_monotonicity (Sequent ctx asm' h'
                                    (zforall vs ztrue $ r0 `zeq` r1))
                    (FunApp g0 xs, FunApp g1 ys)
                        | length xs /= length ys || g0 /= g1 -> Nothing
                        | name f == "=" -> do
                            (_,x,y) <- differs_by_one xs ys
                            return $ apply_monotonicity (Sequent ctx asm' h' $ 
                                FunApp f [x, y])
                        | name g0 `elem` ["and","or","not","=>"] &&
                          name f == "=>" -> do
                                -- and(0,1), or(0,1), 
                                --      =>(1)       -> f.x => f.y -> x => y
                                -- not (0), =>(0)   -> f.x => f.y -> y => x
                                -- | arithmetic relations are not implement
                                -- <=(0)            -> f.x => f.y -> y <= x
                                -- <=(1)            -> f.x => f.y -> x <= y
                                -- +(0,1),-(0)      -> f.x <= f.y -> x <= y
                                -- -(1)             -> f.x <= f.y -> y <= x
                                -- | How would we treat the case of:
                                -- | context => a+b+x R a+b+y
                                -- | we need a means to distinguish an 
                                -- | implication that introduces contextual
                                -- | information
                            x <- mono (name f) (name g0) xs ys
                            return $ apply_monotonicity (Sequent ctx asm' h' x)
--                            let op = name g0
--                                mono i xs
--                                    | (op `elem` ["and","or"]) ||
--                                        (op == "=>" && i == 1)     = FunApp f xs
--                                    |  op == "not" ||
--                                        (op == "=>" && i == 0)     = FunApp f $ reverse xs
--                                    | otherwise                  = error $ "Z3.discharge': unexpected operator / position pair: " ++ op ++ ", " ++ show i
--                            in case differs_by_one xs ys of
--                                Just (i,x,y) -> 
--                                    apply_monotonicity (Sequent ctx asm h' $ 
--                                        mono i [x, y])
--                                Nothing -> 
--                                    po
                    _ -> Nothing
            _ -> Nothing
    where
        shared :: Eq a => [a] -> [a] -> Bool
        shared xs ys = not $ L.null $ intersect xs ys
        mono :: String -> String -> [Expr] -> [Expr] -> Maybe Expr
        mono rel fun xs ys = do
            f       <- M.lookup (rel, fun) m
            (i,x,y) <- differs_by_one xs ys
            g       <- f i
            return $ g x y
        m = M.fromList $
            [ (("=>","and"),const $ Just zimplies)
            , (("=>","or"),const $ Just zimplies)
            , (("=>","not"),const $ Just $ flip zimplies)
            , (("=>","=>"), \i -> Just $ if i == 0 
                                         then flip zimplies 
                                         else zimplies)
            , (("=>","<="), \i -> Just $ if i == 0 
                                         then flip zle 
                                         else zle)
            , (("<=","+"),const $ Just zle)
            , (("<=","-"), \i -> Just $ if i == 0 
                                         then flip zle 
                                         else zle)
            ]

fresh :: String -> S.Set String -> String
fresh name xs = head $ ys `minus` S.elems xs
    where
        ys = name : map f [0..]
        f x = name ++ show x

entailment :: Sequent -> Sequent -> (Sequent,Sequent)
entailment  
    (Sequent (Context srt0 cons0 fun0 def0 dum0) xs0 hs0 xp0) 
    (Sequent (Context srt1 cons1 fun1 def1 dum1) xs1 hs1 xp1) = 
            (po0,po1)
    where
        po0 = Sequent 
            (Context 
                (srt0 `merge` srt1) 
                (cons0 `merge` cons1) 
                (fun0 `merge` fun1) 
                (def0 `merge` def1)
                (dum0 `merge` dum1))
            []
            empty
            $ xp0 `zimplies` xp1 
        po1 = Sequent 
            (Context 
                (srt0 `merge` srt1) 
                (cons0 `merge` cons1) 
                (fun0 `merge` fun1) 
                (def0 `merge` def1)
                (dum0 `merge` dum1))
            xs1
            hs1
            (zall $ xs0 ++ elems hs0)

derive makeNFData ''AbsSequent
