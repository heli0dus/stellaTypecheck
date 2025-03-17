{-# LANGUAGE KindSignatures #-}
{-# LANGUAGE GADTs #-}
{-# LANGUAGE TypeOperators #-}
{-# LANGUAGE FlexibleInstances #-}
{-# LANGUAGE MultiParamTypeClasses #-}
{-# LANGUAGE UndecidableInstances #-}
module Util.Effects where
import qualified Stella.Abs as St
import Control.Algebra
import Control.Effect.State (State, get, modify)
import Data.Map (Map, (!?))
import qualified Data.Map as Map
import Control.Effect.Error
import Control.Effect.Reader (Reader, ask)
import Data.Set (Set)
import qualified Data.Set as Set
import Util.Types

-- Я сначала хотел прикрутить сюда эффекты, но потом понял что эьто съест больше времени чем я могу себе позволить
-- да ещё и без колдунства с эффектами высшего порядка нормально контекст не выражается а с ними я бы ещё больше 
-- времени потратил на воздух. Возможно в следующих этапах прикручу поэтому не удаляю пока

guardError :: Has (Error e) sig m => Bool -> e -> m ()
guardError cond err = if cond then pure () else throwError err

getCtx :: Has (State (Map St.StellaIdent St.Type)) sig m => St.StellaIdent -> m (Maybe St.Type)
getCtx ident = (!? ident) <$> get


updateCtx :: Has (State (Map St.StellaIdent St.Type)) sig m => St.StellaIdent -> St.Type -> m ()
updateCtx ident typ = modify (Map.insert ident typ)

requireCtx :: (Has (State (Map St.StellaIdent St.Type)) sig m, Has (Error TypingError) sig m) => St.StellaIdent -> St.Type -> m ()
requireCtx ident typ = do
    ctx <- get
    let ctxTyp = ctx !? ident
    maybe
        (throwError $ Uncategorized "Identifyer not foud in context")
        (\ty -> guardError (ty == typ) $ Uncategorized "Variable type doesn't match")
        ctxTyp
    
requireExt :: (Has (Reader (Set St.Extension)) sig m, Has (Error TypingError) sig m) => St.Extension -> m ()
requireExt ext = do
    exts <- ask
    guardError (ext `Set.member` exts) $ Uncategorized $ "Required Extension " <> show ext <> " not found in context"