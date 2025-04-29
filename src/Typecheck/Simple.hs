{-# LANGUAGE LambdaCase #-}
module Typecheck.Simple where
import Stella.Abs
import Util.Types
import qualified Data.Map as Map
import qualified Data.Set as Set
import GHC.Float (expts)
import Stella.Par (pMatchCase)

guardWithError :: Bool -> b -> Either b ()
guardWithError cond err = if cond then Right () else Left err

checkProgram :: Program -> TypeCheckResult
checkProgram (AProgram _ exts decls) = do
    initialTypingContext <- collectTypingContext decls
    let ctx = Map.fromList initialTypingContext
    guardWithError (StellaIdent "main" `Map.member` ctx) ERROR_MISSING_MAIN
    foldl (\acc decl -> acc >> checkDecl extnames ctx decl) (Right ()) decls
    where
        extnames= exts >>= (\(AnExtension names) -> names)

collectTypingContext ::  [Decl] -> Either TypingError [(StellaIdent, Type)]
collectTypingContext = traverse extractType
    where
        extractType :: Decl -> Either TypingError (StellaIdent, Type)
        extractType = \case
            DeclFun _ ident params (SomeReturnType retType) _ _ _ -> Right (ident, TypeFun (fmap (\(AParamDecl _ ty) -> ty) params) retType)
            x -> Left $ Uncategorized $ "Unsupported declatation for initial context collecting: " <> show x

checkDecls :: [ExtensionName] -> TypingContext -> [Decl] -> TypeCheckResult
checkDecls exts ctx = foldl (\acc decl -> acc >> checkDecl exts ctx decl) (Right ())

checkDecl :: [ExtensionName] -> TypingContext -> Decl -> TypeCheckResult
checkDecl exts ctx = \case
    DeclFun _ _ [AParamDecl ident ty] (SomeReturnType rettype) _ innerDecls expr -> do
        innetrctx <- collectTypingContext innerDecls
        let newctx = foldl (\c (idt, typ) -> Map.insert idt typ c) ctx innetrctx
        checkDecls exts newctx innerDecls
        checkExpr exts (Map.insert ident ty ctx) rettype expr
    x -> Left $ Uncategorized $ "Unsopported declaration to check type: " <> show x

requireExt :: [ExtensionName] -> ExtensionName -> Either TypingError ()
requireExt exts ext = guardWithError (ext `elem` exts) $ Uncategorized $ "Extension " <> show ext <> " not found in declarations"

requireOneOf :: [ExtensionName] -> [ExtensionName] -> Either TypingError ()
requireOneOf exts targets = guardWithError (any (`elem` exts) targets) $ Uncategorized $ "Extensions " <> show exts <> " not found in declarations"

checkExpr :: [ExtensionName] -> TypingContext -> Type -> Expr -> TypeCheckResult
checkExpr exts ctx ty expr = case expr of
    -- language core
    Abstraction [AParamDecl name ptyp] body -> do
        case ty of
            TypeFun [p] restyp -> do
                guardWithError (ptyp == p) $ ERROR_UNEXPECTED_TYPE_FOR_PARAMETER p ptyp name expr
                checkExpr exts (Map.insert name ptyp ctx) restyp body
            _ -> Left $ ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION ty expr
    Application f [arg] -> do
        appt <- inferExpr exts ctx f
        (argt, restyp) <- case appt of
            TypeFun [p] restyp -> do Right (p, restyp)
            _ -> Left $ ERROR_NOT_A_FUNCTION f
        checkExpr exts ctx argt arg
        guardWithError (restyp == ty) $ ERROR_UNMATCHED_TYPES ty restyp expr
    ConstInt 0 -> case ty of
        TypeNat -> Right ()
        _ ->  Left $ ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION ty expr
    Succ n -> case ty of
        TypeNat -> checkExpr exts ctx TypeNat n
        _ -> Left $ ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION ty expr
    IsZero n -> case ty of
        TypeBool -> checkExpr exts ctx TypeNat n
        _ -> Left $ ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION ty expr
    NatRec n z rec -> do
        checkExpr exts ctx TypeNat n
        checkExpr exts ctx ty      z
        checkExpr exts ctx (TypeFun [TypeNat] $ TypeFun [ty] ty) rec

    ConstTrue  -> case ty of
        TypeBool -> pure ()
        _ -> Left $ ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION ty expr
    ConstFalse -> case ty of
        TypeBool -> pure ()
        _ -> Left $ ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION ty expr
    If cond th els -> do
        checkExpr exts ctx TypeBool cond
        checkExpr exts ctx ty th
        checkExpr exts ctx ty els

    Var x -> do
        xty <- maybe (Left$ ERROR_UNDEFINED_VARIABLE x) Right $ ctx Map.!? x
        guardWithError (ty == xty) $ ERROR_UNMATCHED_TYPES ty xty expr

    -- unit type extension
    ConstUnit -> do
        requireExt exts (ExtensionName "unit-type")
        case ty of
            TypeUnit -> pure ()
            _ -> Left $ ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION ty expr

    -- pairs and tupes
    Tuple exs -> do
        case length exs of
            2 -> do
                requireOneOf exts [ExtensionName "pairs", ExtensionName "tuples"]
            _ -> do
                requireExt exts (ExtensionName "tuples")
        case ty of
            TypeTuple tys -> do
                guardWithError (length exs == length tys) $ ERROR_UNEXPECTED_TUPLE_LENGTH
                foldl (>>) (pure ()) $ checkExpr exts ctx <$> tys <*> exs
            _ -> Left $ ERROR_UNEXPECTED_TUPLE expr

    DotTuple tup idx -> do
        requireOneOf exts [ExtensionName "pairs", ExtensionName "tuples"]
        tuptyp <- inferExpr exts ctx tup
        case tuptyp of
            TypeTuple typs -> if idx < toInteger (length typs) then
                guardWithError (typs !! fromInteger idx /= ty) $ ERROR_UNMATCHED_TYPES ty (typs !! fromInteger idx) expr
                else
                    Left $ ERROR_TUPLE_INDEX_OUT_OF_BOUNDS idx expr (toInteger $ length typs) tuptyp
            _ -> Left $ ERROR_NOT_A_TUPLE tup

    -- records
    Record binds -> do
        requireExt exts (ExtensionName "records")
        case ty of
            TypeRecord tybinds -> let
                recordLabels = (\(ABinding idt _)         -> idt) <$> binds
                typeLabels   = (\(ARecordFieldType idt _) -> idt) <$> tybinds
                labelsNotInRecord = filter (`notElem` recordLabels) typeLabels
                labelsNotInType   = filter (`notElem` typeLabels  ) recordLabels
                in do
                    guardWithError (length (Set.elems $ Set.fromList recordLabels) == length recordLabels) $ ERROR_DUPLICATE_RECORD_FIELDS expr
                    guardWithError (length (Set.elems $ Set.fromList typeLabels) == length typeLabels) $ ERROR_DUPLICATE_RECORD_TYPE_FIELDS ty
                    guardWithError (null labelsNotInType) $ ERROR_UNEXPECTED_RECORD_FIELDS expr ty labelsNotInType
                    guardWithError (null labelsNotInRecord) $ ERROR_MISSING_RECORD_FIELDS expr ty labelsNotInRecord
                    foldl (\prev (ABinding idt ex, ARecordFieldType idt' typ) -> do
                            prev
                            guardWithError (idt == idt') $ ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION ty expr
                            checkExpr exts ctx typ ex
                        )
                        (pure ())
                        (zip binds tybinds)
            _ -> Left $ ERROR_UNEXPECTED_RECORD expr ty

    DotRecord record ident -> do
        requireExt exts (ExtensionName "records")
        rectyp <- inferExpr exts ctx record
        case rectyp of
            TypeRecord tybinds -> let
                typmap = Map.fromList $ (\(ARecordFieldType idt typ) -> (idt, typ)) <$> tybinds
                in maybe
                    (Left $ ERROR_UNEXPECTED_FIELD_ACCESS)
                    (\typ -> guardWithError (ty == typ) $ ERROR_UNMATCHED_TYPES ty typ expr)
                    (typmap Map.!? ident)
            _ -> Left $ ERROR_NOT_A_RECORD record

    -- let bindings
    Let [APatternBinding (PatternVar ident) ex] expr' -> do
        requireExt exts (ExtensionName "let-bindings")
        binderType <- inferExpr exts ctx ex
        let newctx = Map.insert ident binderType ctx
        checkExpr exts newctx ty expr'

    -- type ascription
    TypeAsc term typ -> do
        requireExt exts (ExtensionName "type-ascription")
        checkExpr exts ctx typ term
        guardWithError (typ == ty) $ ERROR_UNMATCHED_TYPES ty typ expr

    -- sum types
    Inl x -> do
        requireExt exts (ExtensionName "sum-types")
        case ty of
            TypeSum lty _ -> checkExpr exts ctx lty x
            _ -> Left $ ERROR_UNEXPECTED_INJECTION expr ty
    Inr x -> do
        requireExt exts (ExtensionName "sum-types")
        case ty of
            TypeSum _ rty -> checkExpr exts ctx rty x
            _ -> Left $ ERROR_UNEXPECTED_INJECTION expr ty

    -- variant types
    -- Здесь что-то будет, но видимо потом
    Variant label ex -> case ty of
        TypeVariant flds -> do
            guardWithError (label `Map.member` variantFieldsToMap flds) $ ERROR_UNEXPECTED_VARIANT_LABEL
        _  -> Left $ ERROR_UNEXPECTED_VARIANT expr ty
        where
            variantFieldsToMap flds = Map.fromList $ (\(AVariantFieldType idt typ) -> (idt, typ)) <$> flds

    Match e cases -> do
        requireOneOf exts [ExtensionName "sum-types", ExtensionName "variants"]
        ety <- inferExpr exts ctx e
        case ety of
            TypeSum lty rty -> checkSumCases exts ctx lty rty ty cases
            TypeVariant flds -> undefined
            _ -> Left $ Uncategorized "Unsupported"
        where
            checkSumCases :: [ExtensionName] -> TypingContext -> Type -> Type -> Type -> [MatchCase] -> TypeCheckResult
            checkSumCases exts ctx lty rty target = \case
                [AMatchCase (PatternInl (PatternVar idt)) exl,  AMatchCase (PatternInr (PatternVar idt')) exr] -> do
                    checkExpr exts (Map.insert idt lty ctx) target exl
                    checkExpr exts (Map.insert idt' rty ctx) target exr
                _ -> undefined


    -- lists
    List elems -> do
        requireExt exts (ExtensionName "lists")
        case ty of
            TypeList elemType -> foldl (\pr cur -> pr >> checkExpr exts ctx elemType cur) (pure ()) elems
            _ -> Left $ ERROR_UNEXPECTED_LIST expr ty
    ConsList x xs -> do
        requireExt exts (ExtensionName "lists")
        case ty of
            TypeList elemType -> do
                checkExpr exts ctx elemType x
                checkExpr exts ctx ty xs
            _ -> Left $ ERROR_UNEXPECTED_LIST expr ty
    Head xs -> do
        requireExt exts (ExtensionName "lists")
        checkExpr exts ctx (TypeList ty) xs
    Tail xs -> do
        requireExt exts (ExtensionName "lists")
        checkExpr exts ctx ty xs
    IsEmpty xs -> do
        requireExt exts (ExtensionName "lists")
        xstyp <- inferExpr exts ctx xs
        case xstyp of
            TypeList _ -> guardWithError (ty == TypeBool) $ ERROR_UNMATCHED_TYPES ty xstyp expr
            _ -> Left $ ERROR_NOT_A_LIST xs

    --fixpoint combinator
    Fix f -> do
        requireExt exts (ExtensionName "fixpoint-combinator")
        checkExpr exts ctx (TypeFun [ty] ty) f

    --natural literals
    ConstInt _ -> do
        requireExt exts (ExtensionName "natural-literals")
        case ty of
            TypeNat -> Right ()
            _ ->  Left $ ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION ty expr

    x -> Left $ Uncategorized $ "Unsupported expression: " <> show x

inferExpr :: [ExtensionName] -> TypingContext -> Expr -> Either TypingError Type
inferExpr exts ctx expr = case expr of
    -- language core
    Abstraction [AParamDecl name ptyp] body -> do
        bodytyp <- inferExpr exts (Map.insert name ptyp ctx) body
        pure $ TypeFun [ptyp] bodytyp
    Application f [arg] -> do
        appt <- inferExpr exts ctx f
        (argt, restyp) <- case appt of
            TypeFun [p] restyp -> do Right (p, restyp)
            _ -> Left $ ERROR_NOT_A_FUNCTION f
        checkExpr exts ctx argt arg
        pure restyp
    ConstInt 0 -> pure TypeNat
    Succ n -> do
        checkExpr exts ctx TypeNat n
        pure TypeNat
    IsZero n -> do
        checkExpr exts ctx TypeNat n
        pure TypeBool
    NatRec n z rec -> do
        checkExpr exts ctx TypeNat n
        zty <- inferExpr exts ctx z
        checkExpr exts ctx (TypeFun [TypeNat] $ TypeFun [zty] zty) rec
        pure zty

    ConstTrue -> pure TypeBool
    ConstFalse -> pure TypeBool
    If cond th els -> do
        checkExpr exts ctx TypeBool cond
        branchType <- inferExpr exts ctx th
        checkExpr exts ctx branchType els
        pure branchType

    Var x -> do
        maybe (Left$ ERROR_UNDEFINED_VARIABLE x) Right $ ctx Map.!? x


    -- unit type extension
    ConstUnit -> do
        requireExt exts (ExtensionName "unit-type")
        pure TypeUnit

    -- pairs and tupes
    Tuple exs -> do
        case length exs of
            2 -> do
                requireOneOf exts [ExtensionName "pairs", ExtensionName "tuples"]
            _ -> do
                requireExt exts (ExtensionName "tuples")
        extyps <- traverse (inferExpr exts ctx) exs
        pure $ TypeTuple extyps
    DotTuple tup idx -> do
        requireOneOf exts [ExtensionName "pairs", ExtensionName "tuples"]
        tuptyp <- inferExpr exts ctx tup
        case tuptyp of
            TypeTuple typs ->
                if idx < toInteger (length typs) then
                    pure $ typs !! fromInteger idx
                else
                    Left $ ERROR_TUPLE_INDEX_OUT_OF_BOUNDS idx expr (toInteger $ length typs) tuptyp
            _ -> Left $ ERROR_NOT_A_TUPLE expr

    -- records
    Record binds -> do
        requireExt exts (ExtensionName "records")
        TypeRecord <$> traverse (\(ABinding idt ex) -> ARecordFieldType idt <$> inferExpr exts ctx ex) binds
    DotRecord record ident -> do
        requireExt exts (ExtensionName "records")
        rectyp <- inferExpr exts ctx record
        case rectyp of
            TypeRecord tybinds -> let
                typmap = Map.fromList $ (\(ARecordFieldType idt typ) -> (idt, typ)) <$> tybinds
                in maybe
                    (Left $ ERROR_MISSING_RECORD_FIELDS record rectyp [ident])
                    Right
                    (typmap Map.!? ident)
            _ -> Left $ ERROR_NOT_A_RECORD record

    -- let bindings
    Let [APatternBinding (PatternVar ident) ex] expr' -> do
        requireExt exts (ExtensionName "let-bindings")
        binderType <- inferExpr exts ctx ex
        let newctx = Map.insert ident binderType ctx
        inferExpr exts newctx expr'

    -- type ascription
    TypeAsc term typ -> do
        requireExt exts (ExtensionName "type-ascription")
        checkExpr exts ctx typ term
        pure typ

    -- sum types
    Inl _ -> do
        requireExt exts (ExtensionName "sum-types")
        Left $ ERROR_AMBIGUOUS_SUM_TYPE expr
    Inr _ -> do
        requireExt exts (ExtensionName "sum-types")
        Left $ ERROR_AMBIGUOUS_SUM_TYPE expr

    -- variant types
    -- Здесь что-то будет, но видимо потом
    Variant label ex -> Left $ ERROR_AMBIGUOUS_VARIANT_TYPE

    Match e cases -> undefined



    -- lists
    List exs -> do
        requireExt exts (ExtensionName "lists")
        case exs of
            [] -> Left $ ERROR_AMBIGUOUS_LIST expr
            (x : xs) -> do
                xty <- inferExpr exts ctx x
                foldl (\pr cur -> pr >> checkExpr exts ctx xty cur) (pure ()) xs
                pure xty
    ConsList x xs -> do
        requireExt exts (ExtensionName "lists")
        xty <- inferExpr exts ctx x
        checkExpr exts ctx (TypeList xty) xs
        pure xty
    Head xs -> do
        requireExt exts (ExtensionName "lists")
        xsty <- inferExpr exts ctx xs
        case xsty of
            TypeList elemType -> pure elemType
            _ -> Left $ ERROR_NOT_A_LIST xs
    Tail xs -> do
        requireExt exts (ExtensionName "lists")
        xsty <- inferExpr exts ctx xs
        case xsty of
            TypeList _ -> pure xsty
            _ -> Left $ ERROR_NOT_A_LIST xs
    IsEmpty xs -> do
        requireExt exts (ExtensionName "lists")
        xstyp <- inferExpr exts ctx xs
        case xstyp of
            TypeList _ -> pure TypeBool
            _ -> Left $ ERROR_NOT_A_LIST xs


    --fixpoint combinator
    Fix f -> do
        requireExt exts (ExtensionName "fixpoint-combinator")
        fty <- inferExpr exts ctx f
        case fty of
            TypeFun [t] t' | t == t' -> pure t
            _ -> Left $ ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION fty f

    --natural literals
    ConstInt _ -> do
        requireExt exts (ExtensionName "natural-literals")
        pure TypeNat

    x -> Left $ Uncategorized $ "Unsupported expression: " <> show x