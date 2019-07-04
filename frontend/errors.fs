module Errors

exception FrontendFatalException of string

exception FrontendException of string

exception FrontendTypeException of string

exception FrontendEquivTypeException of string * string * string

exception FrontendSyntaxException of string
