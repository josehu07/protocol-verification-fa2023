// Model your messages here. This is in its own file, separate from Types.t.dfy,
// because we don't need to trust the messages sent by the protocol for it to be
// correct (hence the .v.dfy extension).

module MessageType {
  datatype Message =
      // DONE: fill in here (solution: 1 line)
    | MigrateMsg(chunk: imap<int, int>)
      // END EDIT
}
