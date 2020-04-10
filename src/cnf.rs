use std::cmp::{min, max};
use rand;
use rand::distributions::IndependentSample;
use rand::StdRng;
use std::collections::{HashSet, HashMap};
use std::iter::FromIterator;



#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
struct VarLabel(u64);

/// Literal, a variable label and its corresponding truth assignment
#[derive(Debug, Clone, PartialEq, Eq, Hash, Copy)]
struct Literal {
    label: VarLabel,
    polarity: bool
}

impl Literal {
    fn get_label(&self) -> VarLabel {
        self.label
    }

    fn get_polarity(&self) -> bool {
        self.polarity
    }

    fn new(label: VarLabel, polarity: bool) -> Literal {
        Literal { label: label, polarity: polarity}
    }
}

#[derive(Debug, Clone, PartialEq, Eq, Hash)]
struct Assignment{
    v: Vec<bool>
}

impl Assignment {
    fn random(len: usize) -> Assignment {
        let mut v = Vec::with_capacity(len);
        for _ in 0..len {
            v.push(rand::random());
        }
        Assignment{ v: v }
    }

    fn rerandomize(self, pos: HashSet<usize>) -> Assignment {
        let mut v = self.v.clone();
        for i in pos {
            v[i] = rand::random();
        }
        Assignment{v: v}
    }
}

#[derive(Debug, Clone, Eq, PartialEq)]
struct Cnf {
    clauses: Vec<Vec<Literal>>,
    deps: Vec<HashSet<usize>>, // for each clause, a vector containing all clauses that share variables with it
    num_vars: usize,
}

impl Cnf {
    fn gen_deps(clauses: &Vec<Vec<Literal>>) -> Vec<HashSet<usize>> {
        let mut r = Vec::new();
        for c1 in 0..(clauses.len()) {
            let mut s = HashSet::new();
            for c2 in 0..(clauses.len()) {
                if c1 == c2 {
                    continue;
                }
                for lit1 in &clauses[c1] {
                    for lit2 in &clauses[c2] {
                        if lit1.get_label() == lit2.get_label() {
                            s.insert(c2);
                        }
                    }
                }
            }
            println!("length of clause {:?}: {:?}", clauses[c1], s.len());
            r.push(s);
        }
        let tot = r.iter().fold(0, |sum, val| sum + val.len());
        println!("average degree: {:?}", (tot as f64) / (r.len() as f64));
        r
    }

    fn from_file(v: String) -> Cnf {
        use dimacs::*;
        let r = parse_dimacs(&v).unwrap();
        let (_, cvec) = match r {
            Instance::Cnf { num_vars, clauses } => (num_vars, clauses),
            _ => panic!(),
        };
        let mut clause_vec: Vec<Vec<Literal>> = Vec::new();
        let mut m = 0;
        for itm in cvec.iter() {
            let mut lit_vec: Vec<Literal> = Vec::new();
            for l in itm.lits().iter() {
                let b = match l.sign() {
                    Sign::Neg => false,
                    Sign::Pos => true,
                };
                // subtract 1, we are 0-indexed
                let lbl = VarLabel(l.var().to_u64() - 1);
                m = max(l.var().to_u64() as usize, m);
                lit_vec.push(Literal::new(lbl, b));
            }
            clause_vec.push(lit_vec);
        }
        let deps = Cnf::gen_deps(&clause_vec);
        Cnf {
            clauses: clause_vec,
            deps: deps,
            num_vars: m,
        }
    }

    /// Produces a set of indices that is true iff the clause at position i is violated by
    /// the assignment
    fn find_bad(&self, assgn: &Assignment) -> HashSet<usize> {
        let mut r = HashSet::new();
        for i in 0..self.clauses.len() {
            let mut bad = true;
            for lit in &self.clauses[i] {
                let VarLabel(idx) = lit.get_label();
                if assgn.v[idx as usize] == lit.get_polarity() {
                    bad = false;
                }
            }
            if bad {
                r.insert(i);
            }
        }
        r
    }

    /// expands a set of clauses to its neighborhood
    fn expand(&self, clauseset: &HashSet<usize>) -> HashSet<usize> {
        let mut r = HashSet::new();
        for c in clauseset {
            r = r.union(&self.deps[*c]).cloned().collect();
        }
        /*
        let mut visited = HashSet::new();
        let mut frontier = Vec::from_iter(clauseset.into_iter());
        while !frontier.is_empty() {
            let cur = frontier.pop().unwrap();
            if visited.contains(cur) {
                continue;
            }
            visited.insert(cur);
            for neighbor in self.deps[*cur] {
                
            }
        }*/
        r
    }

    /// gets the indices of all variables in `clauseset`
    fn var(&self, clauseset: &HashSet<usize>) -> HashSet<usize> {
        let mut r = HashSet::new();
        for i in clauseset {
            for lit in &self.clauses[*i] {
                let VarLabel(x) = lit.get_label();
                r.insert(x as usize);
            }
        }
        r
    }

    fn is_blocked(&self, assgn: &Assignment, restriction: &HashSet<usize>, clause: usize) -> bool {
        // check if they are independent or if the clause is implied
        let mut indep = true;
        let mut implies = false;
        for i in &self.clauses[clause] {
            let VarLabel(l) = i.get_label();
            if restriction.contains(&(l as usize)) {
                indep = false;
                // check if it is implied
                if assgn.v[l as usize] == i.get_polarity() {
                    implies = true;
                }
            }
        }
        return indep || implies;
    }

    /// Produces a clause set that is in the neighborhood of `set` wrt. `assgn`
    /// set contains a vector of clause indices
    /// this follows Algorithm 5 of Guo et al.
    fn find_resample(&self, assgn: &Assignment) -> HashSet<usize> {
        let mut r : HashSet<usize> = self.find_bad(&assgn);
        // let n = Vec::new();
        let mut n : HashSet<usize> = HashSet::new();
        let mut u : HashSet<usize> = self.expand(&r);
        while !u.is_empty() {
            let restr = self.var(&r);
            for i in u {
                if self.is_blocked(&assgn, &restr, i) {
                    r.insert(i);
                } else {
                    n.insert(i);
                }
            }
            u = self.expand(&r).difference(&n).cloned().collect();
        }
        r
    }

    fn partial_rejection(&self) -> Assignment {
        let mut assgn = Assignment::random(self.num_vars);
        let mut is_bad = self.find_bad(&assgn).len() > 0;
        // println!("assignment: {:?}, bad: {:?}", assgn, self.find_bad(&assgn));
        let mut num = 0;
        while is_bad {
            // println!("assignment: {:?}, bad: {:?}", assgn, self.find_bad(&assgn));
            let resample = self.find_resample(&assgn);
            let vars = self.var(&resample);
            // println!("resampling size {:?} out of {:?}", vars.len(), assgn.v.len());
            assgn = assgn.rerandomize(vars);
            is_bad = self.find_bad(&assgn).len() > 0;
            num += 1;
        }
        // println!("resampled {:?} times", num);
        assgn
    }


    fn rand_cnf(rng: &mut StdRng, num_vars: usize, num_clauses: usize) -> Cnf {
        assert!(num_clauses > 2, "requires at least 2 clauses in CNF");
        let vars: Vec<Literal> = (1..num_vars)
            .map(|x| Literal::new(VarLabel(x as u64), rand::random()))
            .collect();
        let range = rand::distributions::Range::new(0, vars.len());
        let clause_size = 3;
        // we generate a random cnf
        let mut clause_vec: Vec<Vec<Literal>> = Vec::new();
        for _ in 0..num_clauses {
            let num_vars = clause_size;
            if num_vars > 1 {
                let mut var_vec: Vec<Literal> = Vec::new();
                for _ in 0..clause_size {
                    let var = vars.get(range.ind_sample(rng)).unwrap().clone();
                    var_vec.push(var);
                }
                clause_vec.push(var_vec);
            } else {
                let var = vars.get(range.ind_sample(rng)).unwrap().clone();
                clause_vec.push(vec!(var));
            }
        }
        let deps = Cnf::gen_deps(&clause_vec);
        Cnf { clauses: clause_vec, deps: deps, num_vars: num_vars }
    }


    fn num_vars(&self) -> usize {
        self.num_vars
    }

    fn clauses(&self) -> &[Vec<Literal>] {
        self.clauses.as_slice()
    }

    fn new(clauses: Vec<Vec<Literal>>) -> Cnf {
        let mut m = 0;
        for clause in clauses.iter() {
            for lit in clause.iter() {
                let VarLabel(x) = lit.get_label();
                m = max(x, m);
            }
        }
        let deps = Cnf::gen_deps(&clauses);
        Cnf { clauses: clauses, deps: deps, num_vars: (m + 1) as usize}
    }
}



static C1_A: &'static str = "
p cnf 227 713
-9 -47 0
-20 -47 0
47 9 20  0
-47 29 0
9 0
";

#[test]
fn test_resample() {
    let cnf = Cnf::from_file(String::from(C1_A));
    // let cnf = Cnf::rand_cnf(&mut StdRng::new().unwrap(), 300, 500);
    let mut results = HashMap::new();
    for _ in 0..1 {
        let res = cnf.partial_rejection();
        *results.entry(res.clone()).or_insert(0) += 1;
        println!("found sample")
    }

    for (key, value) in &results {
        println!("{:?}", value);
    }
}
