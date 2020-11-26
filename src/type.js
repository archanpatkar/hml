// Type checker
// Based on -
// http://dev.stephendiehl.com/fun/type_systems.html#simply-typed-lambda-calculus
// https://www.cs.cornell.edu/courses/cs6110/2013sp/lectures/lec25-sp13.pdf
const { equal } = require("saman");
const { sum, tagged } = require("styp");

const Type = sum("Types", {
    TVar:["v"],
    TCon:["name"],
    TArr:["t1","t2"]
});

// const Scheme = sum("Scheme", {
//     Mono: ["t"],
//     Poly:["var","t"]
// });

const Constraint = tagged("ConstraintEq",["left","right"]);

const TypeEnv = () => new Map();

const TInt = Type.TCon("int");
const TBool = Type.TCon("bool");

const ops = ["ADD", "SUB", "DIV", "MUL"]
const printType = (type) => Array.isArray(type) ? `(${printType(type[0])}->${printType(type[1])})` : type;

// Errors
const genericError = (msg) => { throw new Error(msg) };
const notInScope = (name) => genericError(`Variable --> '${name}' not in Scope`);
const notType = (type,msg) => genericError(`Expected type '${printType(type)}' ${msg}`);
const typeMismatch = (type1,type2) => genericError(`Couldn't match the expected type: ${printType(type1)} with type: ${printType(type2)}`);
const nonFunction = (type) => genericError(`Tried to apply to non-Function type --> ${type}`);

class SymbolTable {
    constructor(parent) {
        this.env = {};
        this.parent = parent;
    }

    addBinding(name, type) {
        this.env[name] = type
    }

    removeBinding(name) {
        delete this.env[name]
    }

    lookUp(name) {
        if (this.env[name]) return this.env[name];
        else if(this.parent) return this.parent.lookUp(name);
        notInScope(name);
    }
}

class TypeChecker {
    constructor() {
        this.sym = new SymbolTable(null);
        this.count = 0;
        this.typeenv = TypeEnv();
        this.constraints = [];
    }

    fresh() {
        return Type.TVar("t" + this.count++);
    }

    addConstraint(type1,type2) {
        this.constraints.push(Constraint(type1,type2));
    }

    unify() {}
    solve() {}

    infer(ast,sym=this.sym) {
        if (ast.node == "literal") 
            return ast.type == "int"? TInt:TBool;
        else if (ast.node == "var") return sym.lookUp(ast.name);
        else if (ast.node == "condition") {
            const cond = this.infer(ast.cond,sym);
            this.addConstraint(cond,TBool);
            const t1 = this.infer(ast.exp1,sym);
            const t2 = this.infer(ast.exp2,sym);
            this.addConstraint(t1,t2);
            return t1;
        }
        else if (ast.node == "lambda") {
            const ne = new SymbolTable(sym);
            const tv = this.fresh();
            ne.addBinding(ast.param, tv);
            const body = this.infer(ast.body,ne);
            return Type.TArr(tv,body);
        }
        else if (ast.node == "apply") {
            const t1 = this.infer(ast.exp1,sym);
            const t2 = this.infer(ast.exp2,sym);
            const tv = this.fresh();
            this.addConstraint(t1,Type.TArr(t2,tv));
            return tv;
        }
        return;
    }

    prove(ast) {
        return printType(this.check(ast))
    }
}


const Lam = (param, type, body) => ({ node: "lambda", param: param, type: type, body: body });
const Lit = (type, val) => ({ node: "literal", type: type, val: val });
const Var = (name) => ({ node: "var", name: name });
const App = (lam, param) => ({ node: "apply", exp1: lam, exp2: param });
const Condition = (cond,e1,e2) => ({ node: "condition", cond:cond, exp1: e1, exp2: e2 });
const BinOp = (op, l, r) => ({ node: op, l: l, r: r });
const UnOp = (op,v) => ({ node: op, val: v });

const tc1 = new TypeChecker();
let code = App(
    Lam("x",null,
        Condition(
            Lit("bool",true),
            Var("x"),
            Lit("int",0)
        )
    ),
    Lit("int",10)
);
console.log(tc1.infer(code).toString());
tc1.constraints.map(c => console.log(c.toString()));

module.exports = TypeChecker;