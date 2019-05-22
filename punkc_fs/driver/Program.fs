open System
open System.IO
open Frontend

[<EntryPoint>]
let main argv =
    let frontend = new Frontend()
    let str = File.ReadAllText argv.[0]
    let stmts = frontend.compile str
    printfn "%A" stmts
    0
