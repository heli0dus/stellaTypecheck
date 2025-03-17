module Util.Types where
import Stella.Abs
import Data.Map (Map)

-- Excepted type goes before actual

data TypingError = 
    ERROR_MISSING_MAIN 
    | ERROR_UNDEFINED_VARIABLE StellaIdent
    | ERROR_UNEXPECTED_TYPE_FOR_EXPRESSION Type Expr
    | ERROR_UNMATCHED_TYPES Type Type Expr
    | ERROR_NOT_A_FUNCTION Expr
    | ERROR_NOT_A_TUPLE Expr
    | ERROR_NOT_A_RECORD Expr
    | ERROR_NOT_A_LIST Expr
    | ERROR_UNEXPECTED_LAMBDA Expr
    | ERROR_UNEXPECTED_TYPE_FOR_PARAMETER Type Type StellaIdent Expr
    | ERROR_UNEXPECTED_TUPLE Expr
    | ERROR_TUPLE_INDEX_OUT_OF_BOUNDS Integer Expr Integer Type
    | ERROR_UNEXPECTED_RECORD Expr Type
    | ERROR_MISSING_RECORD_FIELDS Expr Type [StellaIdent]
    | ERROR_UNEXPECTED_RECORD_FIELDS Expr Type [StellaIdent]
    | ERROR_DUPLICATE_RECORD_FIELDS Expr
    | ERROR_DUPLICATE_RECORD_TYPE_FIELDS Type
    | ERROR_UNEXPECTED_LIST Expr Type
    | ERROR_AMBIGUOUS_LIST Expr
    | Uncategorized String
    deriving Show
type TypeCheckResult = Either TypingError ()
type TypingContext = Map StellaIdent Type