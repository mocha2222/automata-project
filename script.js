// Global variables
let currentAutomaton = null;
let savedAutomata = [];
let selectedAutomatonId = null;

// Finite Automaton class
class FiniteAutomaton {
    constructor(name, states, alphabet, startState, acceptStates, transitions) {
        this.id = Date.now() + Math.random();
        this.name = name;
        this.states = new Set(states);
        this.alphabet = new Set(alphabet);
        this.startState = startState;
        this.acceptStates = new Set(acceptStates);
        this.transitions = new Map();
        this.parseTransitions(transitions);
    }

    parseTransitions(transitionString) {
        const lines = transitionString.trim().split('\n');
        lines.forEach(line => {
            if (line.trim()) {
                const [from, input, to] = line.split(',').map(s => s.trim());
                const key = `${from},${input}`;
                if (!this.transitions.has(key)) {
                    this.transitions.set(key, new Set());
                }
                this.transitions.get(key).add(to);
            }
        });
    }

    isDeterministic() {
        for (const [key, toStates] of this.transitions) {
            if (toStates.size > 1) {
                return false;
            }
        }
        return true;
    }

    acceptsString(inputString) {
        let currentStates = new Set([this.startState]);
        
        for (const symbol of inputString) {
            if (!this.alphabet.has(symbol)) {
                return false;
            }
            
            const nextStates = new Set();
            for (const state of currentStates) {
                const key = `${state},${symbol}`;
                if (this.transitions.has(key)) {
                    for (const nextState of this.transitions.get(key)) {
                        nextStates.add(nextState);
                    }
                }
            }
            currentStates = nextStates;
        }
        
        for (const state of currentStates) {
            if (this.acceptStates.has(state)) {
                return true;
            }
        }
        return false;
    }

    // Updated convertToDFA method - replace the existing one in your FiniteAutomaton class
    convertToDFA() {
        if (this.isDeterministic()) {
            return this;
        }

        const dfaStates = new Set();
        const dfaTransitions = new Map();
        const dfaAcceptStates = new Set();
        const stateQueue = [];
        const stateMap = new Map();

        // Start with epsilon closure of start state (just the start state itself since no epsilon transitions shown)
        const startClosure = new Set([this.startState]);
        stateQueue.push(startClosure);
    
        // Create readable state name for start state
        const startStateName = Array.from(startClosure).length === 1 ? 
            Array.from(startClosure)[0] : 
            Array.from(startClosure).sort().join('-');
    
        stateMap.set(startStateName, startClosure);

        while (stateQueue.length > 0) {
            const currentStateSet = stateQueue.shift();
            const currentStateName = Array.from(currentStateSet).length === 1 ? 
                Array.from(currentStateSet)[0] : 
                Array.from(currentStateSet).sort().join('-');
            
            dfaStates.add(currentStateName);

        // Check if this state should be accepting
            for (const state of currentStateSet) {
                if (this.acceptStates.has(state)) {
                    dfaAcceptStates.add(currentStateName);
                    break;
                }
            }

            // For each symbol in alphabet
            for (const symbol of this.alphabet) {
                const nextStateSet = new Set();
            
                for (const state of currentStateSet) {
                    const key = `${state},${symbol}`;
                    if (this.transitions.has(key)) {
                        for (const nextState of this.transitions.get(key)) {
                            nextStateSet.add(nextState);
                        }
                    }
                }

                if (nextStateSet.size > 0) {
                    const nextStateName = Array.from(nextStateSet).length === 1 ? 
                        Array.from(nextStateSet)[0] : 
                        Array.from(nextStateSet).sort().join('-');
                    
                    dfaTransitions.set(`${currentStateName},${symbol}`, new Set([nextStateName]));

                    if (!stateMap.has(nextStateName)) {
                        stateMap.set(nextStateName, nextStateSet);
                        stateQueue.push(nextStateSet);
                    }
                }
            }
        }

        // Create new DFA
        const dfa = new FiniteAutomaton(
            this.name + '_DFA',
            Array.from(dfaStates),
            Array.from(this.alphabet),
            startStateName,
            Array.from(dfaAcceptStates),
            ''
        );
        dfa.transitions = dfaTransitions;
        return dfa;
    }
    minimize() {
        if (!this.isDeterministic()) {
            throw new Error('Can only minimize deterministic automata');
        }

        // Simple minimization algorithm
        const equivalenceClasses = new Map();
        const states = Array.from(this.states);
        
        // Initial partition: accepting vs non-accepting states
        const accepting = [];
        const nonAccepting = [];
        
        for (const state of states) {
            if (this.acceptStates.has(state)) {
                accepting.push(state);
            } else {
                nonAccepting.push(state);
            }
        }

        let partitions = [];
        if (accepting.length > 0) partitions.push(accepting);
        if (nonAccepting.length > 0) partitions.push(nonAccepting);

        // Refine partitions
        let changed = true;
        while (changed) {
            changed = false;
            const newPartitions = [];

            for (const partition of partitions) {
                const subPartitions = new Map();

                for (const state of partition) {
                    let signature = '';
                    for (const symbol of this.alphabet) {
                        const key = `${state},${symbol}`;
                        if (this.transitions.has(key)) {
                            const nextState = Array.from(this.transitions.get(key))[0];
                            // Find which partition the next state belongs to
                            let partitionIndex = -1;
                            for (let i = 0; i < partitions.length; i++) {
                                if (partitions[i].includes(nextState)) {
                                    partitionIndex = i;
                                    break;
                                }
                            }
                            signature += partitionIndex + ',';
                        } else {
                            signature += '-1,';
                        }
                    }

                    if (!subPartitions.has(signature)) {
                        subPartitions.set(signature, []);
                    }
                    subPartitions.get(signature).push(state);
                }

                if (subPartitions.size > 1) {
                    changed = true;
                }

                for (const subPartition of subPartitions.values()) {
                    newPartitions.push(subPartition);
                }
            }

            partitions = newPartitions;
        }

        // Build minimized automaton
        const minStates = partitions.map((partition, index) => `S${index}`);
        const minTransitions = new Map();
        const minAcceptStates = new Set();
        let minStartState = '';

        // Map old states to new states
        const stateMapping = new Map();
        partitions.forEach((partition, index) => {
            const newState = `S${index}`;
            partition.forEach(oldState => {
                stateMapping.set(oldState, newState);
                if (this.acceptStates.has(oldState)) {
                    minAcceptStates.add(newState);
                }
                if (oldState === this.startState) {
                    minStartState = newState;
                }
            });
        });

        // Build transitions
        for (const [key, toStates] of this.transitions) {
            const [fromState, symbol] = key.split(',');
            const newFromState = stateMapping.get(fromState);
            const oldToState = Array.from(toStates)[0];
            const newToState = stateMapping.get(oldToState);
            
            const newKey = `${newFromState},${symbol}`;
            minTransitions.set(newKey, new Set([newToState]));
        }

        const minimized = new FiniteAutomaton(
            this.name + '_MIN',
            minStates,
            Array.from(this.alphabet),
            minStartState,
            Array.from(minAcceptStates),
            ''
        );
        minimized.transitions = minTransitions;
        return minimized;
    }

    toString() {
        let result = `Automaton: ${this.name}\n`;
        result += `States: {${Array.from(this.states).join(', ')}}\n`;
        result += `Alphabet: {${Array.from(this.alphabet).join(', ')}}\n`;
        result += `Start State: ${this.startState}\n`;
        result += `Accept States: {${Array.from(this.acceptStates).join(', ')}}\n`;
        result += 'Transitions:\n';
        for (const [key, toStates] of this.transitions) {
            const [from, input] = key.split(',');
            for (const to of toStates) {
                result += ` ${from} --> ${input} --> ${to}\n`;
            }
        }
        return result;
    }
        
    convertToRegularExpression() {
        const dfa = this.isDeterministic() ? this : this.convertToDFA();
        return dfa.stateEliminationMethod();
    }

    stateEliminationMethod() {
        const states = Array.from(this.states);
        const n = states.length;

        const stateMap = {};
        states.forEach((state, i) => {
            stateMap[state] = i;
        });

        const virtualStart = n;
        const virtualFinal = n + 1;
        const totalStates = n + 2;

        const R = Array.from({ length: totalStates }, () =>
            Array.from({ length: totalStates }, () => new Set())
        );

        for (const [key, toStates] of this.transitions.entries()) {
            const [from, symbol] = key.split(',');
            const fromIdx = stateMap[from];
            for (const to of toStates) {
                const toIdx = stateMap[to];
                R[fromIdx][toIdx].add(symbol);
            }
        }

        R[virtualStart][stateMap[this.startState]].add('ε');

        for (const acceptState of this.acceptStates) {
            R[stateMap[acceptState]][virtualFinal].add('ε');
        }

        const toRegex = set => {
            if (set.size === 0) return '∅';
            if (set.size === 1) return [...set][0];
            return `(${[...set].join('|')})`;
        };

        for (let k = 0; k < n; k++) {
            for (let i = 0; i < totalStates; i++) {
                for (let j = 0; j < totalStates; j++) {
                    if (i === k || j === k) continue;
                    const ik = toRegex(R[i][k]);
                    const kk = toRegex(R[k][k]);
                    const kj = toRegex(R[k][j]);

                    if (ik === '∅' || kj === '∅') continue;

                    const part = this.concatenateRegex(
                        this.concatenateRegex(ik, this.starRegex(kk)),
                        kj
                    );
                    R[i][j] = new Set([...R[i][j], part]);
                }
            }

            for (let x = 0; x < totalStates; x++) {
                R[x][k] = new Set();
                R[k][x] = new Set();
            }
        }

        const regex = toRegex(R[virtualStart][virtualFinal]);
        return this.simplifyRegex(regex);
    }

    concatenateRegex(r1, r2) {
        if (r1 === '∅' || r2 === '∅') return '∅';
        if (r1 === 'ε') return r2;
        if (r2 === 'ε') return r1;

        const needsParen = r => /\|/.test(r) && !/^\(.+\)$/.test(r);
        return (needsParen(r1) ? `(${r1})` : r1) + (needsParen(r2) ? `(${r2})` : r2);
    }

    unionRegex(r1, r2) {
        if (r1 === '∅') return r2;
        if (r2 === '∅') return r1;
        if (r1 === r2) return r1;

        const parts = new Set();
        for (const p of [r1, r2]) {
            if (p.startsWith('(') && p.endsWith(')')) {
                p.slice(1, -1).split('|').forEach(s => parts.add(s));
            } else {
                parts.add(p);
            }
        }

        return `(${Array.from(parts).join('|')})`;
    }

    starRegex(r) {
        if (r === '∅' || r === 'ε') return 'ε';
        if (r.endsWith('*')) return r;
        if (/^[a-zA-Z0-9]$/.test(r)) return r + '*';
        return `(${r})*`;
    }

    simplifyRegex(regex) {
        if (!regex || regex === '∅') return '∅';
        if (regex === 'ε') return 'ε';

        let result = regex;
        let changed = true;

        while (changed) {
            changed = false;
            const old = result;

            result = result.replace(/ε([a-zA-Z0-9(])/g, '$1');
            result = result.replace(/([a-zA-Z0-9)])ε/g, '$1');
            result = result.replace(/\(([a-zA-Z0-9])\)/g, '$1');
            result = result.replace(/\(∅\|([^)]+)\)/g, '$2');
            result = result.replace(/\(([^)]+)\|∅\)/g, '$1');
            result = result.replace(/\*\*/g, '*');

            if (result !== old) changed = true;
        }

        return result === '' ? 'ε' : result;
    }


}

// UI Functions
function createAutomaton() {
    try {
        const name = document.getElementById('automatonName').value.trim();
        const states = document.getElementById('states').value.trim().split(',').map(s => s.trim());
        const alphabet = document.getElementById('alphabet').value.trim().split(',').map(s => s.trim());
        const startState = document.getElementById('startState').value.trim();
        const acceptStates = document.getElementById('acceptStates').value.trim().split(',').map(s => s.trim());
        const transitions = document.getElementById('transitions').value.trim();

        if (!name || !states[0] || !alphabet[0] || !startState || !acceptStates[0] || !transitions) {
            throw new Error('Please fill in all fields');
        }

        currentAutomaton = new FiniteAutomaton(name, states, alphabet, startState, acceptStates, transitions);
        savedAutomata.push(currentAutomaton);
        
        showResult('createResult', currentAutomaton.toString(), 'success');
        updateAutomataList();
        clearForm();
    } catch (error) {
        showResult('createResult', `Error: ${error.message}`, 'error');
    }
}

function testDeterministic() {
    if (!currentAutomaton) {
        showResult('deterministicResult', 'Error: No automaton selected', 'error');
        return;
    }

    const isDet = currentAutomaton.isDeterministic();
    const result = isDet ? 
        'The automaton IS deterministic (DFA)' : 
        'The automaton is NOT deterministic (NFA)';
    showResult('deterministicResult', result, isDet ? 'success' : 'error');
}

function testString() {
    if (!currentAutomaton) {
        showResult('acceptanceResult', 'Error: No automaton selected', 'error');
        return;
    }

    const testStr = document.getElementById('testString').value;
    const accepts = currentAutomaton.acceptsString(testStr);
    const result = accepts ? 
        `String "${testStr}" is ACCEPTED by the automaton` : 
        `String "${testStr}" is REJECTED by the automaton`;
    showResult('acceptanceResult', result, accepts ? 'success' : 'error');
}

function convertNFAtoDFA() {
    if (!currentAutomaton) {
        showResult('conversionResult', 'Error: No automaton selected', 'error');
        return;
    }

    try {
        const dfa = currentAutomaton.convertToDFA();
        savedAutomata.push(dfa);
        showResult('conversionResult', `Conversion successful!\n\n${dfa.toString()}`, 'success');
        updateAutomataList();
    } catch (error) {
        showResult('conversionResult', `Error: ${error.message}`, 'error');
    }
}

function minimizeDFA() {
    if (!currentAutomaton) {
        showResult('minimizeResult', 'Error: No automaton selected', 'error');
        return;
    }

    try {
        const minimized = currentAutomaton.minimize();
        savedAutomata.push(minimized);
        showResult('minimizeResult', `Minimization successful!\n\n${minimized.toString()}`, 'success');
        updateAutomataList();
    } catch (error) {
        showResult('minimizeResult', `Error: ${error.message}`, 'error');
    }
}

function loadAutomaton() {
    if (!selectedAutomatonId) {
        alert('Please select an automaton to load');
        return;
    }

    const automaton = savedAutomata.find(a => a.id === selectedAutomatonId);
    if (automaton) {
        currentAutomaton = automaton;
        
        // Fill form with automaton data
        document.getElementById('automatonName').value = automaton.name;
        document.getElementById('states').value = Array.from(automaton.states).join(',');
        document.getElementById('alphabet').value = Array.from(automaton.alphabet).join(',');
        document.getElementById('startState').value = automaton.startState;
        document.getElementById('acceptStates').value = Array.from(automaton.acceptStates).join(',');
        
        // Rebuild transitions string
        let transitionsStr = '';
        for (const [key, toStates] of automaton.transitions) {
            const [from, input] = key.split(',');
            for (const to of toStates) {
                transitionsStr += `${from},${input},${to}\n`;
            }
        }
        document.getElementById('transitions').value = transitionsStr.trim();
    }
}

function deleteAutomaton() {
    if (!selectedAutomatonId) {
        alert('Please select an automaton to delete');
        return;
    }

    savedAutomata = savedAutomata.filter(a => a.id !== selectedAutomatonId);
    selectedAutomatonId = null;
    updateAutomataList();
}

function exportAutomata() {
    const data = JSON.stringify(savedAutomata, null, 2);
    const blob = new Blob([data], { type: 'application/json' });
    const url = URL.createObjectURL(blob);
    const a = document.createElement('a');
    a.href = url;
    a.download = 'automata.json';
    a.click();
    URL.revokeObjectURL(url);
}

function updateAutomataList() {
    const listElement = document.getElementById('automataList');
    
    if (savedAutomata.length === 0) {
        listElement.innerHTML = '<p style="color: #6b7280; text-align: center; padding: 20px;">No automata saved yet</p>';
        return;
    }

    listElement.innerHTML = savedAutomata.map(automaton => `
        <div class="automata-item ${selectedAutomatonId === automaton.id ? 'selected' : ''}" 
             onclick="selectAutomaton(${automaton.id})">
            <div class="automata-name">${automaton.name}</div>
            <div class="automata-details">
                States: ${automaton.states.size} | 
                ${automaton.isDeterministic() ? 'DFA' : 'NFA'} | 
                Alphabet: {${Array.from(automaton.alphabet).join(', ')}}
            </div>
        </div>
    `).join('');
}

function selectAutomaton(id) {
    selectedAutomatonId = id;
    updateAutomataList();
}

function switchTab(tabName) {
    // Handle tab switching for different sections
    const tabs = document.querySelectorAll('.tab');
    const contents = document.querySelectorAll('.tab-content');

    tabs.forEach(tab => tab.classList.remove('active'));
    contents.forEach(content => content.classList.remove('active'));

    const activeTab = Array.from(tabs).find(tab => tab.textContent.toLowerCase().includes(tabName.toLowerCase()));
    const activeContent = document.getElementById(tabName);

    if (activeTab) activeTab.classList.add('active');
    if (activeContent) activeContent.classList.add('active');
}

function showResult(elementId, message, type) {
    const element = document.getElementById(elementId);
    element.textContent = message;
    element.className = `result ${type}`;
    element.style.display = 'block';
}

function clearForm() {
    document.getElementById('automatonName').value = '';
    document.getElementById('states').value = '';
    document.getElementById('alphabet').value = '';
    document.getElementById('startState').value = '';
    document.getElementById('acceptStates').value = '';
    document.getElementById('transitions').value = '';
}

function importAutomata() {
    console.log("Starting import process...");
    
    const fileInput = document.createElement('input');
    fileInput.type = 'file';
    fileInput.accept = '.json';
    fileInput.style.display = 'none';
    
    // Add to DOM temporarily
    document.body.appendChild(fileInput);
    
    fileInput.addEventListener('change', function(event) {
        const file = event.target.files[0];
        
        if (!file) {
            console.log("No file selected");
            document.body.removeChild(fileInput);
            return;
        }
        
        console.log("File selected:", file.name);
        
        const reader = new FileReader();
        
        reader.onload = function(e) {
            try {
                const importedData = JSON.parse(e.target.result);
                console.log("Parsed JSON data:", importedData);
                
                if (!Array.isArray(importedData)) {
                    throw new Error("Invalid file format. Expected an array of automata.");
                }
                
                let importedCount = 0;
                let errors = [];
                
                importedData.forEach((data, index) => {
                    try {
                        // Validate required fields
                        if (!data.name || !data.states || !data.alphabet || !data.startState || !data.acceptStates || !data.transitions) {
                            throw new Error(`Missing required fields in automaton ${index + 1}`);
                        }
                        
                        // Convert transitions from exported format back to string format
                        let transitionString = '';
                        if (Array.isArray(data.transitions)) {
                            // Handle array format from export
                            data.transitions.forEach(([key, toStatesArray]) => {
                                const [fromState, symbol] = key.split(',');
                                toStatesArray.forEach(toState => {
                                    transitionString += `${fromState},${symbol},${toState}\n`;
                                });
                            });
                        } else if (data.transitions instanceof Object) {
                            // Handle object format (if transitions were stored as object)
                            for (const [key, toStatesArray] of Object.entries(data.transitions)) {
                                const [fromState, symbol] = key.split(',');
                                if (Array.isArray(toStatesArray)) {
                                    toStatesArray.forEach(toState => {
                                        transitionString += `${fromState},${symbol},${toState}\n`;
                                    });
                                }
                            }
                        } else if (typeof data.transitions === 'string') {
                            // Handle string format (already in correct format)
                            transitionString = data.transitions;
                        }
                        
                        // Create new automaton
                        const newAutomaton = new FiniteAutomaton(
                            data.name,
                            Array.isArray(data.states) ? data.states : Array.from(data.states),
                            Array.isArray(data.alphabet) ? data.alphabet : Array.from(data.alphabet),
                            data.startState,
                            Array.isArray(data.acceptStates) ? data.acceptStates : Array.from(data.acceptStates),
                            transitionString.trim()
                        );
                        
                        // Generate new unique ID
                        newAutomaton.id = Date.now() + Math.random() + importedCount;
                        
                        savedAutomata.push(newAutomaton);
                        importedCount++;
                        
                    } catch (error) {
                        console.warn(`Error importing automaton ${index + 1}:`, error.message);
                        errors.push(`Automaton ${index + 1}: ${error.message}`);
                    }
                });
                
                // Update the UI
                updateAutomataList();
                
                // Show results
                if (importedCount > 0) {
                    let message = `Successfully imported ${importedCount} automaton(s)!`;
                    if (errors.length > 0) {
                        message += `\n\nWarnings:\n${errors.join('\n')}`;
                    }
                    alert(message);
                } else {
                    alert("No automata could be imported. Please check the file format.");
                }
                
            } catch (error) {
                console.error("Import error:", error);
                alert(`Error importing file: ${error.message}`);
            } finally {
                // Clean up
                if (document.body.contains(fileInput)) {
                    document.body.removeChild(fileInput);
                }
            }
        };
        
        reader.onerror = function() {
            alert("Error reading file");
            console.error("FileReader error");
            if (document.body.contains(fileInput)) {
                document.body.removeChild(fileInput);
            }
        };
        
        // Start reading the file
        reader.readAsText(file);
    });
    
    // Trigger file dialog
    fileInput.click();
}
function convertFAToRegex() {
    if (!currentAutomaton) {
        showResult('faToRegexResult', 'Error: No automaton selected', 'error');
        return;
    }

    try {
        const regex = currentAutomaton.convertToRegularExpression();
        showResult('faToRegexResult', `Regular Expression: ${regex}`, 'success');
    } catch (error) {
        showResult('faToRegexResult', `Error: ${error.message}`, 'error');
    }
}

// Initialize the app
updateAutomataList();