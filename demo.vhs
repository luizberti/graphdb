# graphdb demo tape
# run: vhs demo.vhs

Output demo.gif
Set Theme "Catppuccin Mocha"
Set FontSize 15
Set Width 900
Set Height 600
Set Padding 16
Set TypingSpeed 30ms

Hide
Type "cargo run"
Enter
Sleep 2s
Show

Sleep 1s

# Load movie dataset
Type "eval movies.edn"
Sleep 500ms
Enter
Sleep 2s

# Show all datoms
Type "dump"
Sleep 500ms
Enter
Sleep 3s

# Basic query: all movie titles
Type "[:find ?title :where [?m :movie/title ?title]]"
Sleep 500ms
Enter
Sleep 2s

# Join query: who directed Inception?
Type `[:find ?name :where [?m :movie/title "Inception"] [?m :movie/director ?d] [?d :person/name ?name]]`
Sleep 500ms
Enter
Sleep 2s

# All Nolan movies
Type `[:find ?title ?year :where [?d :person/name "Christopher Nolan"] [?m :movie/director ?d] [?m :movie/title ?title] [?m :movie/year ?year]]`
Sleep 500ms
Enter
Sleep 2s

# Predicate filter: movies after 2015
Type "[:find ?title ?year :where [?m :movie/title ?title] [?m :movie/year ?year] [(gt ?year 2015)]]"
Sleep 500ms
Enter
Sleep 2s

# Aggregates: year stats
Type "[:find (count ?m) (min ?y) (max ?y) (avg ?y) :where [?m :movie/title _] [?m :movie/year ?y]]"
Sleep 500ms
Enter
Sleep 2s

# Live transaction: add Interstellar
Type `[:+ 105 :movie/title "Interstellar"] [:+ 105 :movie/year 2014] [:+ 105 :movie/director #ref 1]`
Sleep 500ms
Enter
Sleep 2s

# Verify it shows up
Type `[:find ?title ?year :where [?d :person/name "Christopher Nolan"] [?m :movie/director ?d] [?m :movie/title ?title] [?m :movie/year ?year]]`
Sleep 500ms
Enter
Sleep 3s

# Exit
Type "exit"
Sleep 300ms
Enter
Sleep 1s
