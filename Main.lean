import LeanDatalog.Run

def main (args: List String): IO UInt32 :=
  if args.contains "-i" || args.contains "--interactive"
  then runInteractive
  else runBatch
