import Data.List (nub, sort, groupBy, elemIndex, (\\), intersect)
import Data.Maybe (fromJust, fromMaybe)

type State = Int
type Symbol = Char
type Partition = [[State]]
type TransitionTable = [((State, Symbol), State)]

data NFA = NFA { nfaStates :: [State]
               , nfaAlphabet :: [Symbol]
               , nfaDelta :: [(State, Symbol, [State])]
               , nfalambdaTransitions :: [(State, [State])]
               , nfaStartState :: State
               , nfaAcceptStates :: [State]
               } deriving (Show)

data DFA = DFA { dfaStates :: [State]
               , dfaAlphabet :: [Symbol]
               , dfaDelta :: [(State, Symbol, State)]
               , dfaStartState :: State
               , dfaAcceptStates :: [State]
               } deriving (Show)

powerSet :: [State] -> [[State]]
powerSet [] = [[]]
powerSet (x:xs) = powerSet xs ++ map (x:) (powerSet xs)

-- computes lambda closure of a state in an NFA
lambdaClosure :: NFA -> State -> [State]
lambdaClosure nfa s = epsClosHelper nfa [s] where
  lamClosHelper :: NFA -> [State] -> [State]
  lamClosHelper _ [] = []
  lamClosHelper nfa (x:xs) =
    case lookup x (nfalambdaTransitions nfa) of
      Nothing -> x : lamClosHelper nfa xs
      Just reachableStates -> x : lamClosHelper nfa ((reachableStates ++ xs) \\ [x])

-- converts an NFA to a DFA using powerset construction method
nfa2dfa :: NFA -> DFA
nfa2dfa nfa = DFA
    { dfaStates = [0..(length powerset - 1)]
    , dfaAlphabet = nfaAlphabet nfa
    , dfaDelta = buildDelta (nfaDelta nfa) powerset
    , dfaStartState = fromJust $ elemIndex (lambdaClosure nfa (nfaStartState nfa)) powerset
    , dfaAcceptStates = findAcceptStates powerset (nfaAcceptStates nfa)
    }
  where
    powerset = powerSet (nub $ concatMap (\s -> lambdaClosure nfa s) (nfaStates nfa))
    buildDelta :: [(State, Symbol, [State])] -> [[State]] -> [(State, Symbol, State)]
    buildDelta transitions powerset = [(i, a, targetStateIndex) |
                                       (i, states) <- zip [0..] powerset,
                                       a <- nfaAlphabet nfa,
                                       let targetStates = nub $ concat [delta | state <- states, (s, sym, delta) <- transitions, s == state, sym == a],
                                       let lambdaTargetStates = nub $ concatMap (\s -> lambdaClosure nfa s) targetStates,
                                       let targetStateIndex = fromJust $ elemIndex (sort lambdaTargetStates) (map sort powerset)
                                      ]
    findAcceptStates :: [[State]] -> [State] -> [State]
    findAcceptStates powerset acceptStates = [i | (i, states) <- zip [0..] powerset, not (null (states `intersect` acceptStates))]

-- Hopcroft's algorithm for DFA minimization
minimizeDFA :: DFA -> DFA
minimizeDFA dfa = let dfa' = removeDeadStates $ removeUnreachableStates dfa
                      initPartition = initialPartition dfa'
                      transitionTable = createTransitionTable (dfaDelta dfa')
                      finalPartition = partitionDFA initPartition transitionTable (dfaAlphabet dfa')
                      newStates = zip [0..] $ filter (not . null) finalPartition
                      newStartState = renameState (dfaStartState dfa') newStates
                      newAcceptStates = nub $ map (\s -> renameState s newStates) (dfaAcceptStates dfa')
                      newDelta = [(renameState s newStates, a, renameState sp newStates) 
                                  | (s, a, sp) <- dfaDelta dfa']
                  in DFA (map fst newStates) (dfaAlphabet dfa') (nub newDelta) newStartState newAcceptStates

-- splitting the states to accepting and non-accepting partitions
initialPartition :: DFA -> Partition
initialPartition dfa = [dfaAcceptStates dfa, dfaStates dfa \\ dfaAcceptStates dfa]

-- reformatting the delta to a format used in transition table 
createTransitionTable :: [(State, Symbol, State)] -> TransitionTable
createTransitionTable delta = [((s, a), sp) | (s, a, sp) <- delta]

-- refine the partition until it can't be refined any further
partitionDFA :: Partition -> TransitionTable -> [Symbol] -> Partition
partitionDFA p tt alphabet = 
  let p' = refine p tt alphabet in 
  if p' == p then p 
    else partitionDFA p' tt alphabet

-- concats refined groups into a partition
refine :: Partition -> TransitionTable -> [Symbol] -> Partition
refine p tt alphabet = concat [splitGroup g tt p alphabet | g <- p]

-- groups equivalent states based on the transition function using a lambda function checking equivalence on all symbols from the alphabet
splitGroup :: [State] -> TransitionTable -> Partition -> [Symbol] -> Partition
splitGroup g tt p alphabet = groupBy (\s1 s2 -> all (\a -> findGroup (findTransition s1 a tt) p == findGroup (findTransition s2 a tt) p) alphabet) g

-- returns the target state after transition from s on symbol a according to the transition table tt
findTransition :: State -> Symbol -> TransitionTable -> State
findTransition s a tt = fromMaybe s $ lookup (s, a) tt

-- returns the index of the group to which this state belongs based on the partition p
findGroup :: State -> Partition -> Int
findGroup s p = fromJust $ elemIndex True $ map (elem s) p

-- maps states in the old DFA to the states of the new minimized DFA 
renameState :: State -> [(State, [State])] -> State
renameState s ss = fromMaybe (-1) $ lookup True [(s `elem` g, n) | (n, g) <- ss]

-- helper function to find the reachable states of a DFA
reachableStates :: DFA -> [State]
reachableStates dfa = dfs (dfaStartState dfa) [] where
  dfs current visited
    | current `elem` visited = visited
    | otherwise = foldl (flip dfs) (current:visited) (successors current)

  successors state = [s' | (s, _, s') <- dfaDelta dfa, s == state]

-- removes states not reachable from the start state
removeUnreachableStates :: DFA -> DFA
removeUnreachableStates dfa = 
       let reachables = reachableStates dfa
           newStates = intersect reachables (dfaStates dfa)
           newDelta = [(s, a, sp) | (s, a, sp) <- dfaDelta dfa, s `elem` newStates, sp `elem` newStates]
           newAcceptStates = intersect reachables (dfaAcceptStates dfa)
       in dfa {dfaStates = newStates, dfaDelta = newDelta, dfaAcceptStates = newAcceptStates}

-- helper function to find the live states of a DFA
liveStates :: DFA -> [State]
liveStates dfa = dfs (dfaAcceptStates dfa) [] where
  dfs [] visited = visited
  dfs (x:xs) visited
    | x `elem` visited = dfs xs visited
    | otherwise = dfs (predecessors x ++ xs) (x:visited)

  predecessors state = [s | (s, _, s') <- dfaDelta dfa, s' == state]

-- removes states from which no accepting state can be reached
removeDeadStates :: DFA -> DFA
removeDeadStates dfa = 
       let lives = liveStates dfa
           newStates = intersect lives (dfaStates dfa)
           newDelta = [(s, a, sp) | (s, a, sp) <- dfaDelta dfa, s `elem` newStates, sp `elem` newStates]
           newAcceptStates = intersect lives (dfaAcceptStates dfa)
       in dfa {dfaStates = newStates, dfaDelta = newDelta, dfaAcceptStates = newAcceptStates}

-- testing example for NFA2DFA conversion and minimization
ex0 = NFA {nfaStates = [0,1,2,3], nfaAlphabet = "ab", nfaDelta = [(0,'a',[1]),(0,'b',[3]),(1,'a',[1]),(1,'b',[0])], nfaStartState = 0, nfaAcceptStates = [1], nfalambdaTransitions = [(0,[1])]}

-- testing example for DFA minimization
ex1 = DFA {dfaStates = [0,1,2,3], dfaAlphabet = "ab", dfaDelta = [(0,'a',1),(0,'b',3),(1,'a',1),(1,'b',0)], dfaStartState = 0, dfaAcceptStates = [1]}

-- testing example for DFA minimization
ex2 = DFA {dfaStates = [0,1,2], dfaAlphabet = "ab", dfaDelta = [(0,'a',0),(0,'b',1),(1,'a',0),(1,'b',2),(2,'a',2),(2,'b',1)], dfaStartState = 0, dfaAcceptStates = [1]}

-- larger testing example for NFA2DFA conversion and minimization
ex3 = NFA { nfaStates = [0, 1, 2, 3, 4, 5, 6, 7, 8]
          , nfaAlphabet = "abcd"
          , nfaDelta = [ (0, 'a', [1, 4])
                       , (0, 'b', [2])
                       , (1, 'b', [2])
                       , (2, 'a', [6])
                       , (2, 'c', [1])
                       , (3, 'b', [4])
                       , (3, 'c', [6])
                       , (4, 'a', [3])
                       , (4, 'c', [7])
                       , (5, 'a', [2])
                       , (5, 'd', [6])
                       , (6, 'a', [7])
                       , (6, 'b', [8])
                       , (7, 'a', [0])
                       , (7, 'b', [1])
                       , (8, 'a', [7])
                       , (8, 'b', [0])
                       , (8, 'c', [2])
                       , (8, 'd', [4])
                       ]
          , nfaStartState = 0
          , nfaAcceptStates = [1, 7]
          , nfalambdaTransitions = [(0, [3]), (1, [5])]
          }

-- final function to convert an lambda-NFA to a reduced DFA
nfa2mindfa :: NFA -> DFA
nfa2mindfa nfa = minimizeDFA $ nfa2dfa nfa