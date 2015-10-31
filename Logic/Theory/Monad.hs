module Logic.Theory.Monad where

assert' :: Loc -> ExprP -> M ()
assert' loc stmt = M $ tell 
        [ empty_theory 
            { _fact = singleton (label "") x }]
    where
        x = either (error . unlines . L.map (locMsg loc ++)) id 
            $ zcast bool $ withForall stmt

assert :: ExpQ
assert = withLoc 'assert'

dummy :: VarSignature s => String -> s -> M ExprP
dummy n s = M $ do
    let v = varDecl n s
    tell [ empty_theory & dummies .~ singleton n v ]
    return $ Right $ Word v

command :: forall s. (FromList (FunType s) ExprP, Signature s)
        => String -> s -> M (FunType s)
command n s = do
    f <- function n s
    let proxy = Proxy :: Proxy s
        cmd = Command ('\\':n) n (len' proxy) (from_list f)
    M $ tell [ empty_theory
        { _notation = empty_notation & commands .~ [cmd] } ]
    return f

function :: Signature s => String -> s -> M (FunType s)
function n s = M $ do
    tell [empty_theory 
        { _funs = singleton n (funDecl n s) } ]
    return $ utility n s

operator :: (Signature s, FunType s ~ (ExprP -> ExprP -> ExprP))
         => String -> String -> s -> M (Operator,ExprP -> ExprP -> ExprP)
operator op tag s = do
    f <- function tag s
    let binop = BinOperator tag op f
    M $ tell [empty_theory 
            { _notation = empty_notation & new_ops .~ [Right binop] } ]
    return (Right binop,f)

unary :: (Signature s, FunType s ~ (ExprP -> ExprP))
      => String -> String -> s -> M (Operator,ExprP -> ExprP)
unary op tag s = do
    f <- function tag s
    let unop = UnaryOperator tag op f
    M $ tell [empty_theory 
            { _notation = empty_notation & new_ops .~ [Left unop] } ]
    return (Left unop,f)

preserve :: Fun -> [String] -> M ()
preserve rel fun = M $ tell [empty_theory
    & syntacticThm.monotonicity .~ M.fromList (P.preserve rel fun) ]

associativity :: String -> ExprP -> M ()
associativity fun e = M $ tell [empty_theory
    & syntacticThm.associative .~ M.singleton fun e] 

left_associativity :: [Operator] -> M ()
left_associativity ops = M $ tell [empty_theory
    { _notation = empty_notation & left_assoc .~ [L.map (fromRight $ $myError "") ops] }]

right_associativity :: [Operator] -> M ()
right_associativity ops = M $ tell [empty_theory
    { _notation = empty_notation & right_assoc .~ [L.map (fromRight $ $myError "") ops] }]

precedence :: [Operator] 
           -> [[Operator]]
           -> [Operator]
           -> M ()
precedence vs ops us = M $ tell [empty_theory 
    { _notation = empty_notation & prec .~ [vs : ops ++ [us]] }]

type_param :: M Type
type_param = M $ do
    n <- get
    put (n+1)
    return $ VARIABLE $ "t" ++ show n

sort :: TypeSignature s => String -> M s
sort n = M $ do
    let (r,s) = mkSort n
    tell [empty_theory { _types = singleton n s } ]
    return r

sort_def :: TypeDefSignature s => String -> s -> M s
sort_def n f = M $ do
    let (r,s) = mkSortDef n f
    tell [empty_theory { _types = singleton n s } ]
    return r    

param_to_var :: Expr -> Expr
param_to_var e = evalState (param_to_varE e) (0,variables e,M.empty)

param_to_varE :: Expr -> State (Int,S.Set String,Map String String) Expr
param_to_varE e = do
    e' <- rewriteM param_to_varE e
    case e' of
        FunApp (Fun ps n lift args rt) xs -> do
            FunApp <$> (Fun <$> mapM param_to_varT ps 
                            <*> pure n 
                            <*> pure lift 
                            <*> mapM param_to_varT args 
                            <*> param_to_varT rt) 
                   <*> pure xs
        _ -> return e'

param_to_varT :: Type -> State (Int,S.Set String,Map String String) Type
param_to_varT t@(VARIABLE _) = return t
param_to_varT (GENERIC n) = do
        ns <- use trans
        case M.lookup n ns of
            Just n' -> return $ VARIABLE n'
            Nothing -> do
                n' <- next_free
                _3 %= M.insert n n'
                return $ VARIABLE n'
    where
        count = _1
        vars  = _2
        trans = _3
        next_free = do
            i <- use count
            _1 += 1 -- count
            vs <- use vars 
            if ("t" ++ show i) `S.member` vs 
                then next_free
                else return $ "t" ++ show i
param_to_varT t = rewriteM param_to_varT t

newtype M a = M (RWS () [Theory] Int a)
    deriving (Applicative,Functor,Monad)

clash :: (Show a, Ord a)
      => (thy -> Map a b) -> [thy] -> Map a b
clash f xs 
        | L.null es = M.unions $ L.map f xs
        | otherwise = error $ format "Name clash with: {0}" $ intercalate "," (L.map show es)
    where
        es = keys $ M.unions $ do
            (x,ys) <- zip xs $ drop 1 $ tails xs
            y      <- ys
            return $ M.intersection (f x) (f y)

mzforall' :: [ExprP] -> ExprP -> ExprP -> ExprP
mzforall' vs r t = do
    vs' <- sequence vs >>= mapM (\e -> do
        case e of
            Word v -> return v
            _ -> Left ["Cannot quantify over expressions"])
    mzforall vs' r t

mzexists' :: [ExprP] -> ExprP -> ExprP -> ExprP
mzexists' vs r t = do
    vs' <- sequence vs >>= mapM (\e -> do
        case e of
            Word v -> return v
            _ -> Left ["Cannot quantify over expressions"])
    mzexists vs' r t

