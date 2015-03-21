module Logic.Expr.PrettyPrint 
    ( pretty_print' )
where

    -- Modules
import Logic.Expr.Classes

    -- Libraries
import Control.Monad.Reader


pretty_print' :: Tree t => t -> String
-- pretty_print' t = unlines $ pretty_print $ as_tree t 
pretty_print' t = unlines $ map toString $ as_list $ fst $ runReader (pretty_print_aux $ as_tree t) ""

data Line = Line String String

toString :: Line -> String
toString (Line xs ys) = xs ++ ys

line :: Line -> String
line (Line _ ys) = ys

type M = Reader String
type X = (List Line,Int)

data List a = Ls [a] a

appendL :: List a -> List a -> List a
appendL (Ls xs x) (Ls ys y) = Ls (xs ++ [x] ++ ys) y

tell' :: String -> M X
tell' xs = do
    ys <- ask
    return $ (Ls [] $ Line ys xs,length xs+1)

appendall :: [(List a, Int)] -> (List a, Int)
appendall ((x0,n):(x1,m):xs) = appendall $ (appendL x0 x1, m+n) : xs
appendall [x] = x
appendall _ = error "appendall: empty list"

cons :: a -> [a] -> List a
cons x xs = Ls (init ys) (last ys)
    where
        ys = x:xs

uncons :: List a -> (a -> [a] -> b) -> b
uncons (Ls xs x) f = f (head zs) (tail zs)
    where
        zs = xs ++ [x]

as_list :: List a -> [a]
as_list (Ls xs x) = xs ++ [x]

pretty_print_aux :: StrList -> M X
pretty_print_aux (Str xs) = tell' xs
pretty_print_aux (List []) = tell' "()"
pretty_print_aux (List ys@(x:xs)) = 
        case x of
            Str y    -> do
                zz <- mapM pretty_print_aux xs
                let one_line' = concatMap (" " ++) $ concatMap (map line . as_list . fst) zz
                    k = sum $ map snd zz
                if k <= 50
                then tell' $ "(" ++ y ++ one_line' ++ ")"
                else do
                    zs <- prefix_first ("(" ++ y ++ " ") $
                        mapM pretty_print_aux xs
                    return $ add_to_last ")" $ appendall zs
            List _ -> do
                zs <- prefix_first "( " $
                    mapM pretty_print_aux ys
                return $ add_to_last " )" $ appendall zs
    where
        prefix_first :: String -> M [X] -> M [X]
        prefix_first xs cmd = do
            let k = length xs
            ys <- indent k cmd 
            case ys of
                [] -> (:[]) `liftM` tell' xs
                (ls, n):ys -> 
                    uncons ls $ \(Line m y) zs ->
                    return $ (cons (Line (take (length m - k) m) (xs ++ y)) zs, n+k):ys
        indent n cmd = do
            local (margin n ++) cmd
        margin n = replicate n ' '
        add_to_last suff (Ls xs (Line x y),k) = (Ls xs (Line x $ y++suff),k)
  
-- pretty_print :: StrList -> [String]
-- pretty_print (Str xs) = [xs]
-- pretty_print (List []) = ["()"]
-- pretty_print (List ys@(x:xs)) = 
--         case x of
--             Str y    -> 
--                 if length one_line <= 50
--                 then ["(" ++ y ++ " " ++ one_line ++ ")"]
--                 else
--                     zipWith (++)
--                         (("(" ++ y ++ " "):repeat (margin (length y + 2)))
--                         (add_to_last ")" zs)
--             List _ -> zipWith (++)
--                 ("( ":repeat (margin 2))
--                 (add_to_last " )" zs')
--     where
--         margin n = replicate n ' '
--         add_to_last suff xs = 
--             case reverse xs of
--                 y:ys -> reverse ( (y++suff):ys )
--                 []        -> [suff]
--         zs = concatMap pretty_print xs
--         zs' = concatMap pretty_print ys
--         one_line = intercalate " " zs
