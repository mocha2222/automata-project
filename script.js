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

    convertToDFA() {
        if (this.isDeterministic()) {
            return this;
        }

        const dfaStates = new Set();
        const dfaTransitions = new Map();
        const dfaAcceptStates = new Set();
        const stateQueue = [];
        const stateMap = new Map();

        // Start with epsilon closure of start state
        const startClosure = new Set([this.startState]);
        stateQueue.push(startClosure);
        stateMap.set(Array.from(startClosure).sort().join(','), startClosure);

        while (stateQueue.length > 0) {
            const currentStateSet = stateQueue.shift();
            const currentStateName = Array.from(currentStateSet).sort().join(',');
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
                    const nextStateName = Array.from(nextStateSet).sort().join(',');
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
            Array.from(stateMap.keys())[0],
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
                result += `  δ(${from}, ${input}) = ${to}\n`;
            }
        }
        return result;
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

// Initialize the app
updateAutomataList();