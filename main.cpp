#include <iostream>
#include <string>
#include <map>
#include <set>
#include <vector>
#include <sstream>
#include <algorithm>
#include <memory>
#include <fstream>

class Grammar {
private:
    std::map<std::string, std::vector<std::string>> rules;
    std::vector<std::string> non_terminals;
    std::set<std::string> terminals;

public:
    Grammar(const std::map<std::string, std::vector<std::string>> &rules) : rules(rules) {
        for (const auto &rule: rules) {
            non_terminals.push_back(rule.first);
        }
        terminals = getTerminals();
    }

    std::set<std::string> getTerminals() {
        std::set<std::string> terminals;
        for (const auto &rule: rules) {
            for (const auto &production: rule.second) {
                for (char symbol: production) {
                    std::string s(1, symbol); // Convert char to string
                    if (std::find(non_terminals.begin(), non_terminals.end(), s) == non_terminals.end()) {
                        terminals.insert(s);
                    }
                }
            }
        }
        return terminals;
    }

    const std::map<std::string, std::vector<std::string>> &getRules() const {
        return rules;
    }

    const std::vector<std::string> &getNonTerminals() const {
        return non_terminals;
    }

    const std::set<std::string> &getTerminalsSet() const {
        return terminals;
    }
};

std::set<std::string> computeFirst(const Grammar &grammar, const std::string &symbol,
                                   std::map<std::string, std::set<std::string>> &first_cache) {
    if (first_cache.find(symbol) != first_cache.end()) {
        return first_cache[symbol];
    }

    std::set<std::string> first_set;

    if (grammar.getTerminalsSet().find(symbol) != grammar.getTerminalsSet().end()) {
        first_set.insert(symbol);
        first_cache[symbol] = first_set;
        return first_set;
    }

    for (const auto &production: grammar.getRules().at(symbol)) {
        if (production == "e") {
            first_set.insert("e");
        } else {
            for (char s: production) {
                std::string sym(1, s);
                std::set<std::string> first_s = computeFirst(grammar, sym, first_cache);
                first_set.insert(first_s.begin(), first_s.end());
                if (first_s.find("e") == first_s.end()) {
                    break;
                }
            }
        }
    }

    first_cache[symbol] = first_set;
    return first_set;
}

std::set<std::string> computeFollow(
        const Grammar &grammar,
        const std::string &symbol,
        std::map<std::string, std::set<std::string>> &first_cache,
        std::map<std::string, std::set<std::string>> &follow_cache) {

    // If the FOLLOW set is already computed, return it.
    if (follow_cache.find(symbol) != follow_cache.end()) {
        return follow_cache[symbol];
    }

    std::set<std::string> follow_set;

    // The start symbol always has '$' in its FOLLOW set.
    if (symbol == "S") {
        follow_set.insert("$");
    }

    // Iterate over all productions in the grammar.
    for (const auto &rule: grammar.getRules()) {
        const std::string &non_terminal = rule.first;
        for (const auto &production: rule.second) {
            size_t pos = production.find(symbol);
            while (pos != std::string::npos && pos < production.size()) {
                // Check if the symbol is not at the end of the production
                if (pos + 1 < production.size()) {
                    std::string next_symbol(1, production[pos + 1]);
                    std::set<std::string> first_next = computeFirst(grammar, next_symbol, first_cache);

                    // Add everything from FIRST(next_symbol) except epsilon to FOLLOW(symbol)
                    for (const auto &terminal: first_next) {
                        if (terminal != "e") {
                            follow_set.insert(terminal);
                        }
                    }

                    // If epsilon is in FIRST(next_symbol), add FOLLOW(non_terminal) to FOLLOW(symbol)
                    if (first_next.find("e") != first_next.end()) {
                        std::set<std::string> follow_next = computeFollow(grammar, non_terminal, first_cache,
                                                                          follow_cache);
                        follow_set.insert(follow_next.begin(), follow_next.end());
                    }
                } else {
                    // If the symbol is at the end of the production, add FOLLOW(non_terminal) to FOLLOW(symbol)
                    std::set<std::string> follow_next = computeFollow(grammar, non_terminal, first_cache, follow_cache);
                    follow_set.insert(follow_next.begin(), follow_next.end());
                }

                // Find next occurrence in the production
                pos = production.find(symbol, pos + 1);
            }
        }
    }

    // Cache the result.
    follow_cache[symbol] = follow_set;
    return follow_set;
}

std::map<std::pair<std::string, std::string>, std::string> buildParsingTable(const Grammar &grammar,
                                                                             const std::map<std::string, std::set<std::string>> &first_sets,
                                                                             const std::map<std::string, std::set<std::string>> &follow_sets) {
    std::map<std::pair<std::string, std::string>, std::string> parsing_table;

    for (const auto &rule: grammar.getRules()) {
        const auto &non_terminal = rule.first;
        for (const auto &production: rule.second) {
            std::set<std::string> first_production;
            bool contains_epsilon = false;

            for (char ch: production) { // if production is a std::string, each symbol is a char
                std::string symbol(1, ch); // Convert char to std::string

                // Now we use 'symbol' which is a std::string to search in first_sets.
                auto first_symbol_iter = first_sets.find(symbol);
                if (first_symbol_iter != first_sets.end()) {
                    const auto &first_symbol = first_symbol_iter->second; // Using iterator to access the pair's second element
                    for (const std::string &terminal: first_symbol) {
                        if (terminal != "e") {
                            first_production.insert(terminal); // Inserting std::string into std::set<std::string>
                        }
                    }
                    if (first_symbol.find("e") != first_symbol.end()) {
                        contains_epsilon = true;
                    } else {
                        break;
                    }
                } else {
                    first_production.insert(symbol); // Make sure symbol is a std::string
                    break;
                }
            }

            if (contains_epsilon) {
                first_production.insert("e");
            }

            for (const auto &terminal: first_production) {
                if (terminal != "e") {
                    auto key = std::make_pair(non_terminal, terminal);
                    if (parsing_table.find(key) == parsing_table.end()) {
                        parsing_table[key] = production;
                    } else {
                        std::string error_message =
                                "Grammar is not LL(1): Conflict at (" + non_terminal + ", " + terminal + ")";
                        throw std::logic_error(error_message);
                    }
                }
            }

            if (first_production.find("e") != first_production.end()) {
                for (const auto &terminal: follow_sets.at(non_terminal)) {
                    auto key = std::make_pair(non_terminal, terminal);
                    if (parsing_table.find(key) == parsing_table.end()) {
                        parsing_table[key] = production;
                    } else {
                        std::string error_message =
                                "Grammar is not LL(1): Conflict at (" + non_terminal + ", " + terminal + ")";
                        throw std::logic_error(error_message);
                    }
                }
            }
        }
    }

    return parsing_table;
}

std::set<std::string> findEpsilonProducingNonTerminals(const Grammar &grammar) {
    std::set<std::string> epsilon_producers;

    // Initial pass: find non-terminals with direct epsilon productions
    for (const auto &rule: grammar.getRules()) {
        const auto &non_terminal = rule.first;
        const auto &productions = rule.second;
        for (const auto &production: productions) {
            if (production == "e") {
                epsilon_producers.insert(non_terminal);
                break; // Found epsilon, no need to check other productions
            }
        }
    }

    // Iteratively find non-terminals that can produce epsilon through other non-terminals
    bool changed;
    do {
        changed = false;
        for (const auto &rule: grammar.getRules()) {
            const auto &non_terminal = rule.first;
            for (const auto &production: rule.second) {
                bool all_produce_epsilon = true;
                for (const auto &symbol: production) {
                    // Convert the character to a string for comparison
                    std::string symbol_str(1, symbol);
                    if (epsilon_producers.find(symbol_str) == epsilon_producers.end()) {
                        all_produce_epsilon = false;
                        break; // At least one symbol cannot produce epsilon
                    }
                }
                if (all_produce_epsilon && epsilon_producers.find(non_terminal) == epsilon_producers.end()) {
                    epsilon_producers.insert(non_terminal);
                    changed = true;
                    break; // Non-terminal can produce epsilon, no need to check other productions
                }
            }
        }
    } while (changed);

    return epsilon_producers;
}

Grammar parseGrammarFromText(const std::string &text) {
    std::map<std::string, std::vector<std::string>> rules;
    std::istringstream stream(text);
    std::string line;

    while (std::getline(stream, line)) {
        auto arrow_pos = line.find("->");
        if (arrow_pos != std::string::npos) {
            std::string lhs = line.substr(0, arrow_pos);
            std::string rhs = line.substr(arrow_pos + 3); // Length of "→" is 3 bytes

            // Trim whitespace from lhs
            lhs.erase(lhs.begin(), std::find_if(lhs.begin(), lhs.end(), [](unsigned char ch) {
                return !std::isspace(ch);
            }));
            lhs.erase(std::find_if(lhs.rbegin(), lhs.rend(), [](unsigned char ch) {
                return !std::isspace(ch);
            }).base(), lhs.end());

            // Split rhs on '|'
            std::vector<std::string> productions;
            std::istringstream prod_stream(rhs);
            std::string prod;
            while (std::getline(prod_stream, prod, '|')) {
                // Trim whitespace from prod
                prod.erase(prod.begin(), std::find_if(prod.begin(), prod.end(), [](unsigned char ch) {
                    return !std::isspace(ch);
                }));
                prod.erase(std::find_if(prod.rbegin(), prod.rend(), [](unsigned char ch) {
                    return !std::isspace(ch);
                }).base(), prod.end());

                productions.push_back(prod);
            }

            rules[lhs] = productions;
        }
    }

    return Grammar(rules);
}


class RecursiveDescentParser {
private:
    std::vector<std::string> tokens;
    size_t current_token_index;

public:
    RecursiveDescentParser(const std::vector<std::string> &tokens) : tokens(tokens), current_token_index(0) {}

    std::string lookAhead() {
        if (current_token_index < tokens.size()) {
            return tokens[current_token_index];
        }
        return "";  // Using an empty string to signify the end of input
    }

    const std::vector<std::string> &getTokens() const {
        return tokens;
    }

    size_t getCurrentTokenIndex() const {
        return current_token_index;
    }

    bool consume(const std::string &expected_token) {
        if (lookAhead() == expected_token) {
            current_token_index++;
            return true;
        }
        return false;
    }

    // Grammar rules implementation
    bool A() {
        if (B()) {
            if (A_prime()) {
                return true;
            }
        }
        return false;
    }

    bool A_prime() {
        if (consume("+")) {
            if (B()) {
                if (A_prime()) {
                    return true;
                }
            }
            return false;
        }
        return true;  // Epsilon production
    }

    bool B() {
        if (C()) {
            if (B_prime()) {
                return true;
            }
        }
        return false;
    }

    bool B_prime() {
        if (consume("*")) {
            if (C()) {
                if (B_prime()) {
                    return true;
                }
            }
            return false;
        }
        return true;  // Epsilon production
    }

    bool C() {
        if (consume("(")) {
            if (A()) {
                if (consume(")")) {
                    return true;
                }
            }
            return false;
        } else if (consume("a")) {
            return true;
        }
        return false;
    }

    bool parse() {
        return A() && current_token_index == tokens.size();
    }
};

class Node {
private:
    std::string type;
    std::vector<std::shared_ptr<Node>> children;
    std::string value;

public:
    // Constructor for nodes with children and optional value
    Node(const std::string &type, const std::vector<std::shared_ptr<Node>> &children, const std::string &value = "")
            : type(type), children(children), value(value) {}

    // Constructor for leaf nodes with value
    Node(const std::string &type, const std::string &value)
            : type(type), value(value) {}

    // Constructor for leaf nodes without value
    Node(const std::string &type) : type(type) {}

    // Getters for type, children, and value
    std::string getType() const { return type; }

    const std::vector<std::shared_ptr<Node>> &getChildren() const { return children; }

    std::string getValue() const { return value; }
};

class ASTRecursiveDescentParser : public RecursiveDescentParser {
public:
    using RecursiveDescentParser::RecursiveDescentParser;  // Inherit constructors

    std::shared_ptr<Node> A() {
        auto t_node = B();
        if (t_node) {
            auto e_prime_node = A_prime();
            if (e_prime_node) {
                return std::make_shared<Node>("A", std::vector<std::shared_ptr<Node>>{t_node, e_prime_node});
            }
        }
        return nullptr;
    }

    std::shared_ptr<Node> A_prime() {
        if (consume("+")) {
            auto b_node = B();
            if (b_node) {
                auto a_prime_node = A_prime();
                if (a_prime_node) {
                    return std::make_shared<Node>("A'", std::vector<std::shared_ptr<Node>>{
                            std::make_shared<Node>("op", std::vector<std::shared_ptr<Node>>{}, "+"),
                            b_node, a_prime_node});
                }
            }
            return nullptr;
        }
        return std::make_shared<Node>("A'", std::vector<std::shared_ptr<Node>>{std::make_shared<Node>("e")});
    }

    std::shared_ptr<Node> B() {
        auto c_node = C();
        if (c_node) {
            auto b_prime_node = B_prime();
            if (b_prime_node) {
                return std::make_shared<Node>("B", std::vector<std::shared_ptr<Node>>{c_node, b_prime_node});
            }
        }
        return nullptr;
    }

    std::shared_ptr<Node> B_prime() {
        if (consume("*")) {
            auto c_node = C();
            if (c_node) {
                auto b_prime_node = B_prime();
                if (b_prime_node) {
                    return std::make_shared<Node>("B'", std::vector<std::shared_ptr<Node>>{
                            std::make_shared<Node>("op", std::vector<std::shared_ptr<Node>>{}, "*"),
                            c_node, b_prime_node});
                }
            }
            return nullptr;
        }
        return std::make_shared<Node>("B'", std::vector<std::shared_ptr<Node>>{std::make_shared<Node>("e")});
    }

    std::shared_ptr<Node> C() {
        if (consume("(")) {
            auto a_node = A();
            if (a_node && consume(")")) {
                return std::make_shared<Node>("C", std::vector<std::shared_ptr<Node>>{a_node});
            }
            return nullptr;
        } else if (consume("a")) {
            return std::make_shared<Node>("C", std::vector<std::shared_ptr<Node>>{std::make_shared<Node>("a")});
        }
        return nullptr;
    }

    std::shared_ptr<Node> parse() {
        auto ast_root = A();
        if (ast_root && getCurrentTokenIndex() == getTokens().size()) {
            return ast_root;
        }
        return nullptr;
    }
};

void visualizeAst(const std::shared_ptr<Node> &node, int depth = 0) {
    if (!node) return;

    // Print indentation based on the depth of the current node
    std::string indent(depth * 2, ' '); // 2 spaces per level of depth
    std::cout << indent;

    // Print the current node's type and value
    std::cout << node->getType();
    if (!node->getValue().empty()) {
        std::cout << " (" << node->getValue() << ")";
    }
    std::cout << std::endl;

    // Recursively print each child with increased depth
    for (const auto &child: node->getChildren()) {
        visualizeAst(child, depth + 1);
    }
}

std::set<std::string> computeFirstK(const Grammar &grammar, const std::vector<std::string> &sequence, int k,
                                    std::map<std::string, std::set<std::string>> &first_cache) {
    std::set<std::string> first_k_set;

    if (sequence.empty()) {
        first_k_set.insert("e");
        return first_k_set;
    }

    if (sequence.size() == 1) {
        auto first_1_set = computeFirst(grammar, sequence[0], first_cache);
        for (const auto &item: first_1_set) {
            if (item != "e") {
                first_k_set.insert(item.substr(0, k));
            } else {
                first_k_set.insert("e");
            }
        }
        return first_k_set;
    }

    for (size_t i = 0; i < sequence.size(); ++i) {
        const auto &symbol = sequence[i];
        auto first_i = computeFirst(grammar, symbol, first_cache);
        std::set<std::string> new_items;

        for (const auto &item_prev: first_k_set) {
            for (const auto &item_cur: first_i) {
                if (item_cur != "e") {
                    std::string combined = item_prev + item_cur;
                    new_items.insert(combined.substr(0, k));
                }
            }
        }

        if (first_i.find("e") != first_i.end()) {
            new_items.insert("e");
            first_k_set = new_items;
        } else {
            first_k_set = new_items;
            break;
        }
    }

    return first_k_set;
}

std::vector<std::string> splitProductionIntoSymbols(const std::string &production) {
    std::istringstream iss(production);
    std::vector<std::string> symbols;
    std::string symbol;

    while (iss >> symbol) {
        symbols.push_back(symbol);
    }

    return symbols;
}


std::map<std::pair<std::string, std::string>, std::vector<std::string>>
buildParsingTableK(const Grammar &grammar, std::map<std::string, std::set<std::string>> &first_k_sets,
                   const std::map<std::string, std::set<std::string>> &follow_sets, int k) {
    std::map<std::pair<std::string, std::string>, std::vector<std::string>> parsing_table;

    for (const auto &rule: grammar.getRules()) {
        const auto &non_terminal = rule.first;
        for (const auto &production: rule.second) {
            std::vector<std::string> sequence;
            for (char c: production) {
                sequence.push_back(std::string(1, c)); // Convert each char to a string and add to the sequence
            }
            auto first_k_production = computeFirstK(grammar, sequence, k, first_k_sets);
            for (const auto &lookahead_seq: first_k_production) {
                if (lookahead_seq != "e") {
                    auto key = std::make_pair(non_terminal, lookahead_seq);
                    if (parsing_table.find(key) == parsing_table.end()) {
                        // Assuming that you have split the production into a vector of strings.
                        std::vector<std::string> production_vector = splitProductionIntoSymbols(production);

// Now you can use production_vector to assign to the parsing table.
                        parsing_table[key] = production_vector;
                    } else {
                        std::string error_msg =
                                "Grammar is not LL(" + std::to_string(k) + "): Conflict at (" + non_terminal + ", " +
                                lookahead_seq + ")";
                        throw std::logic_error(error_msg);
                    }
                }
            }

            if (first_k_production.find("e") != first_k_production.end()) {
                for (const auto &terminal: follow_sets.at(non_terminal)) {
                    // Assuming terminal is a string, taking the first 'k' characters for the lookahead
                    std::string lookahead = terminal.substr(0, k);
                    auto key = std::make_pair(non_terminal, lookahead);
                    if (parsing_table.find(key) == parsing_table.end()) {
                        std::vector<std::string> production_vector = splitProductionIntoSymbols(production);
                        parsing_table[key] = production_vector;
                    } else {
                        std::string error_msg =
                                "Grammar is not LL(" + std::to_string(k) + "): Conflict at (" + non_terminal + ", " +
                                lookahead + ")";
                        throw std::logic_error(error_msg);
                    }
                }
            }
        }
    }

    return parsing_table;
}

int main() {
    setlocale(LC_CTYPE, "Greek");
    std::ifstream inputFile("grammarll1.txt");
    if (!inputFile.is_open()) {
        std::cerr << "Unable to open file\n";
        return 1;
    }

    std::stringstream buffer;
    buffer << inputFile.rdbuf();
    std::string grammarText = buffer.str();
    Grammar arithmetic_grammar = parseGrammarFromText(grammarText);

    std::cout << "Rules of parsed grammar" << std::endl;
    for (const auto &rule: arithmetic_grammar.getRules()) {
        std::cout << rule.first << " -> ";
        for (const auto &production: rule.second) {
            std::cout << production;
            if (&production != &rule.second.back()) { // Check if not the last element
                std::cout << " | ";
            }
        }
        std::cout << std::endl;
    }

    std::map<std::string, std::set<std::string>> first_cache;
    std::map<std::string, std::set<std::string>> follow_cache;
    std::map<std::string, std::set<std::string>> first_sets;
    std::map<std::string, std::set<std::string>> follow_sets;

    for (const auto &nt: arithmetic_grammar.getNonTerminals()) {
        first_sets[nt] = computeFirst(arithmetic_grammar, nt, first_cache);
    }

    for (const auto &nt: arithmetic_grammar.getNonTerminals()) {
        follow_sets[nt] = computeFollow(arithmetic_grammar, nt, first_cache, follow_cache);
    }

    std::cout << "First_1" << std::endl;
    for (const auto &pair: first_sets) {
        std::cout << pair.first << ": {";
        for (const auto &symbol: pair.second) {
            std::cout << symbol << " ";
        }
        std::cout << "}" << std::endl;
    }

    std::cout << "Follow_1" << std::endl;
    for (const auto &pair: follow_sets) {
        std::cout << pair.first << ": {";
        for (const auto &symbol: pair.second) {
            std::cout << symbol << " ";
        }
        std::cout << "}" << std::endl;
    }

    auto parsing_table = buildParsingTable(arithmetic_grammar, first_sets, follow_sets);

    std::cout << "Parsing Table" << std::endl;
    for (const auto &entry: parsing_table) {
        const auto &key = entry.first; // The key is a pair (non-terminal, terminal)
        const auto &value = entry.second; // The value is the production rule as a string

        std::cout << "Non-terminal: " << key.first << ", Terminal: " << key.second << " => Production: " << value
                  << std::endl;
    }
    auto epsilon_producing_non_terminals = findEpsilonProducingNonTerminals(arithmetic_grammar);

    std::cout << "Epsilon producing non terminals" << std::endl;
    for (const auto &nt: epsilon_producing_non_terminals) {
        std::cout << nt << " ";
    }
    std::cout << std::endl;


    std::ifstream tokensFile("tokens.txt");
    if (!tokensFile.is_open()) {
        std::cerr << "Unable to open tokens file\n";
        return 1;
    }

    std::string tokensString;
    std::getline(tokensFile, tokensString);
    std::vector<std::string> tokens;
    std::istringstream stream(tokensString);
    std::string token;
    char delimiter = ' ';

    while (std::getline(stream, token, delimiter)) {

        tokens.push_back(token);
    }

    std::vector<std::string> sample_tokens = tokens;
    RecursiveDescentParser parser(sample_tokens);
    bool parse_result = parser.parse();
    std::cout << "Is parsed?" << std::endl;
    std::cout << (parse_result ? "Success" : "Failure") << std::endl;


    ASTRecursiveDescentParser ast_parser(sample_tokens);

    std::shared_ptr<Node> ast_root = ast_parser.parse();

    if (ast_root) {
        std::cout << "AST:" << std::endl;
        visualizeAst(ast_root);
    } else {
        std::cout << "Parsing failed" << std::endl;
    }

    std::map<std::string, std::set<std::string>> first_k_cache;
    std::map<std::string, std::set<std::string>> first_k_sets;

    for (const auto &nt: arithmetic_grammar.getNonTerminals()) {
        first_k_sets[nt] = computeFirstK(arithmetic_grammar, {nt}, 2, first_k_cache);
    }

    std::cout << "First_k:" << std::endl;
    for (const auto &pair: first_k_sets) {
        std::cout << pair.first << ": {";
        for (const auto &symbol: pair.second) {
            std::cout << symbol << " ";
        }
        std::cout << "}" << std::endl;
    }

    // Define a grammar for LL(2) analysis
    std::ifstream inputFilek("grammarllk.txt");
    if (!inputFilek.is_open()) {
        std::cerr << "Unable to open file\n";
        return 1;
    }

    std::stringstream bufferk;
    bufferk << inputFilek.rdbuf();
    std::string grammarTextk = bufferk.str();
    Grammar ll2_grammar = parseGrammarFromText(grammarTextk);

    std::cout << "Rules of parsed grammar" << std::endl;
    for (const auto &rule: ll2_grammar.getRules()) {
        std::cout << rule.first << " -> ";
        for (const auto &production: rule.second) {
            std::cout << production;
            if (&production != &rule.second.back()) {
                std::cout << " | ";
            }
        }
        std::cout << std::endl;
    }


    std::map<std::string, std::set<std::string>> first_k_cache_ll2, first_k_sets_ll2, follow_cache_ll2, follow_sets_ll2;

    for (const auto &nt: ll2_grammar.getNonTerminals()) {
        first_k_sets_ll2[nt] = computeFirstK(ll2_grammar, {nt}, 2, first_k_cache_ll2);
    }

    std::cout << "First_k:" << std::endl;
    for (const auto &pair: first_k_sets_ll2) {
        std::cout << pair.first << ": {";
        for (const auto &symbol: pair.second) {
            std::cout << symbol << " ";
        }
        std::cout << "}" << std::endl;
    }

    for (const auto &nt: ll2_grammar.getNonTerminals()) {
        follow_sets_ll2[nt] = computeFollow(ll2_grammar, nt, first_k_cache_ll2, follow_cache_ll2);
    }

    std::cout << "Follow_k:" << std::endl;
    for (const auto &pair: follow_sets_ll2) {
        std::cout << pair.first << ": {";
        for (const auto &symbol: pair.second) {
            std::cout << symbol << " ";
        }
        std::cout << "}" << std::endl;
    }

    auto parsing_table_ll2 = buildParsingTableK(ll2_grammar, first_k_sets_ll2, follow_sets_ll2, 2);
    std::cout << "LL(2) Parsing Table:" << std::endl;
    for (const auto &entry: parsing_table_ll2) {
        const auto &key = entry.first; // The key is a pair of non-terminal and a string of k terminals
        const auto &value = entry.second; // The value is a vector of strings (productions)
        std::cout << "Non-terminal: " << key.first << ", Lookahead: " << key.second << " => Productions: ";
        for (const auto &prod: value) {
            std::cout << prod << " ";
        }
        std::cout << std::endl;
    }

    return 0;
}
