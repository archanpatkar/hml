#!/usr/bin/env node
const readline = require('readline');
const { Interpreter, modes } = require("./eval");

const machine = new Interpreter();
const rl = readline.createInterface({
  input: process.stdin,
  output: process.stdout,
  prompt: 'hml> '
});

console.log(
`
:::    :::::::    :::: :::        
:+:    :+:+:+:+: :+:+:+:+:        
+:+    +:++:+ +:+:+ +:++:+        
+#++:++#+++#+  +:+  +#++#+        
+#+    +#++#+       +#++#+        
#+#    #+##+#       #+##+#        
###    ######       #############       
`);
console.log("hml (mini-ML w/ Hindley-Milner-Damas) 0.0.1");
console.log("");

rl.prompt();

let pcons = false;

rl.on('line', (input) => {
    if(input == "help") {
        console.log("Enter type <name> to get the type, where name is a valid let binding in the environment")
        console.log("Enter mode <m> where m in [value, name, need] to change evaluation method")
        console.log("Enter 'clear' to clean the console")
        console.log("Enter 'exit' or Ctrl + c to exit")
    }
    else if(input == "clear") console.clear();
    else if(input == "exit") {
        rl.close();
        console.log("");
        console.log("Goodbye!");
        return;
    }
    else if(input.startsWith("mode")) {
        let mode = modes[input.split(" ")[1]];
        if(mode) machine.setMode(mode)
        else console.log("Please specify a proper mode");
    }
    else if(input.startsWith("type")) {
        let name = input.split(" ")[1];
        if(name) console.log(machine.infer.getType(name.trim()));
        else console.log(machine.infer.getTypeEnv().join("\n"));
    }
    else if(input.startsWith("constraints")) pcons = !pcons;
    else {
        try {
            const {output, type, constraints} = machine.evaluate(input);
            console.log(`${type}: ${output}`);
            if(pcons) {
                console.log("Constraints");
                console.log(constraints);
            }
        }
        catch (e) {
            console.log(`Error -> ${e.message}`)
        }
    }
    rl.prompt();
});