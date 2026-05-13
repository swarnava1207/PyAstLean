import PyAstLean.PyGens

def catch_loop := fun num ↦
  Id.run do
    for i in PyAstLean.pyRange num do
      try
        if i == (3 : Int) then
          throwThe String (String.append "ValueError: " (ToString.toString "i cannot be 3"))
        else
          if i == (5 : Int) then
            throwThe String (String.append "ZeroDivisionError: " (ToString.toString "i cannot be 5"))
          else
            let _ := ()
      catch caught =>
        if String.startsWith caught "ValueError:" then
          do
            let e := caught
            let _ :=
              print
                (String.append
                  (String.append (String.append (String.append "" "Caught ValueError at i=") (ToString.toString i))
                    ": ")
                  (ToString.toString e))
        else
          if String.startsWith caught "ZeroDivisionError:" then
            do
              let e := caught
              let _ :=
                print
                  (String.append
                    (String.append
                      (String.append (String.append "" "Caught ZeroDivisionError at i=") (ToString.toString i)) ": ")
                    (ToString.toString e))
          else
            throwThe String caught
