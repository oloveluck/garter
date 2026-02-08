let () =
  let s = new Server.garter_server in
  let server = Linol_lwt.Jsonrpc2.create_stdio ~env:() s in
  Linol_lwt.run
    (Linol_lwt.Jsonrpc2.run server
       ~shutdown:(fun () -> s#get_status = `ReceivedExit))
