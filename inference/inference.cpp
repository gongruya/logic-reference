#include <iostream>
#include <fstream>
#include <vector>
#include <string>
#include <sstream>
#include <unordered_map>
#include <unordered_set>
#include <numeric>

using namespace std;

template<typename T>
inline ostream& operator<<(ostream& out, const vector <T>& v) {     //Overloading vector <<
    out << "[";
    if (v.empty()) {
        return out << "]";
    }
    for (int i = 0; i < v.size() - 1; ++i) {
        out << v[i] << ", ";
    }
    out << v.back();
    out << "]";
    return out;
}
void trim(string& s) {
    if (s == "") {
        return;
    }
    while (s.length() > 0 && s.back() == ' ') {
        s.pop_back();
    }
    if (s == "") {
        return;
    }
    int i;
    for (i = 0; i < s.length() && s[i] == ' '; ++i) {}
    s = s.substr(i);
}
inline void tokenization(const string s, vector <string>& arr, const char delimiter) {
    stringstream ss(s);
    string t;
    while (getline(ss, t, delimiter)) {
        arr.push_back(t);
    }
}
inline bool isVar(const string s) {
    for (const auto& e: s) {
        if ( !((e <= 'z' && e >= 'a') || isdigit(e)) ) {
            return false;
        }
    }
    return true;
}


class Unification {
private:
    unordered_map<string, string> rules;        //var -> const/var
    bool failure;
public:
    Unification(const bool failure = false) {
        this -> failure = failure;
    }
    bool addRule(const string first, const string second) {
        if (first == second) {
            failure = true;
            return false;
        }
        if (!isVar(first)) {                   //Must be variable
            failure = true;
            return false;
        }
        rules[first] = second;
        return true;
    }
    bool hasKey(const string key) const {
        return rules.count(key) > 0;
    }
    const string& operator[](const string key) {
        return rules[key];
    }
    friend ostream& operator<<(ostream& out, const Unification& e) {
        if (e.fail()) {
            return out << "FAILED";
        }
        vector<string> tmp;
        for (const auto entry: e.rules) {
            tmp.push_back(entry.first + "/" + entry.second);
        }
        out << tmp;
        return out;
    }
    bool fail() const {
        return failure;
    }
    static Unification unify(const vector<string>& x, const vector<string>& y, Unification theta) {
        Unification ret;
        
        if (theta.fail()) {
            return Unification(true);
        }
        if (x.size() != y.size()) {
            return Unification(true);
        }
        if (x.size() == 1) {
            return unify(x[0], y[0], theta);
        }
        
        vector<string> xRest(x.begin() + 1, x.end());
        vector<string> yRest(y.begin() + 1, y.end());
        
        return unify(xRest, yRest, unify(x[0], y[0], theta));
    }
private:
    static Unification unify(string x, string y, Unification theta) {        //variable
        if (theta.fail()) {
            return Unification(true);
        }
        if (x == y) {
            return theta;
        }
        if (isVar(x)) {
            return unifyVar(x, y, theta);
        }
        if (isVar(y)) {
            return unifyVar(y, x, theta);
        }
        return Unification(true);
    }
    static Unification unifyVar(const string var, const string x, Unification theta) {
        if (theta.hasKey(var)) {
            return unify(theta[var], x, theta);
        }
        if (theta.hasKey(x)) {
            return unify(var, theta[x], theta);
        }
        Unification ret = theta;
        ret.addRule(var, x);
        return ret;
    }
};


class Predicate {
private:
    vector<string> args;                        //Variables/Constants
    string name;                                //Predicate name
    bool negation;                              //Is there a negation?
public:
    Predicate() {}
    Predicate(string s) {
        trim(s);
        if (s[0] == '~') {
            negation = true;
            s.erase(s.begin());
        } else {
            negation = false;
        }
        
        /*
         * Parsing variables;
         */
        
        int i;
        for (i = 0; i < s.length() && s[i] != '('; ++i) {
            name += s[i];
        }
        s.erase(0, i + 1);
        s.erase(s.end() - 1);
        
        tokenization(s, args, ',');
    }
    
    void standardize(int id) {
        for (auto& e: args) {
            if (isVar(e)) {
                e += to_string(id);
            }
        }
    }
    
    friend ostream& operator<<(ostream& out, const Predicate& e) {
        out << (e.negation? "-": "+") << e.name << e.args;
        return out;
    }
    bool empty() const {
        return name == "" && args.empty();
    }
    
    bool allConst() const {
        for (const auto& e: args) {
            if (isVar(e)) {
                return false;
            }
        }
        return true;
    }
    
    string str() const {
        stringstream ss;
        ss << *this;
        return ss.str();
    }
    
    bool match(const Predicate other) const {
        return getNegation() == other.getNegation() && getName() == other.getName() && getArgNum() == other.getArgNum();
    }
    
    Predicate substitute(Unification u) const {             //Non mutator
        Predicate res = *this;
        for (auto& var: res.args) {
            if (u.hasKey(var)) {
                var = u[var];
            }
        }
        return res;
    }
    bool operator==(const Predicate& other) {
        if (negation != other.negation) {
            return false;
        }
        if (name != other.name) {
            return false;
        }
        if (args.size() != other.args.size()) {
            return false;
        }
        for (int i = 0; i < args.size(); ++i) {
            if (args[i] != other.args[i]) {
                return false;
            }
        }
        return true;
    }
    bool operator!=(const Predicate& other) {
        return !(*this == other);
    }
    const vector<string>& getArgs() const {
        return args;
    }
    string getName() const {
        return name;
    }
    bool getNegation() const {
        return negation;
    }
    int getArgNum() const {
        return args.size();
    }
};


class Sentence {
private:
    vector<Predicate> left;
    Predicate right;
public:
    Sentence() {}
    Sentence(string s) {
        trim(s);
        int inf = s.find("=>");
        if (inf == string::npos) {
            right = Predicate(s);
        } else {
            string leftS = s.substr(0, inf);
            string rightS = s.substr(inf + 2);              //Remove =>
            trim(leftS);
            trim(rightS);
            right = Predicate(rightS);
            
            vector<string> leftConjunction;
            tokenization(leftS, leftConjunction, '^');
            for (auto e: leftConjunction) {
                left.push_back(Predicate(e));
            }
        }
    }
    void standardize(int id) {
        right.standardize(id);
        for (auto& e: left) {
            e.standardize(id);
        }
    }
    friend ostream& operator<<(ostream& out, const Sentence& e) {
        if (e.isFact()) {
            out << e.right;
        } else {
            out << e.left << " -> " << e.right;
        }
        return out;
    }
    bool isFact() const {
        return left.empty();
    }
    const Predicate& getRight() const {
        return right;
    }
    const vector<Predicate>& getLeft() const {
        return left;
    }
};


class KnowledgeBase {
private:
    vector<Sentence> kb;
    //"Globals" used for DFS
    Predicate goalOrigin;
    unordered_set<string> visited;
    int stdID;
public:
    KnowledgeBase() {}
    void addSentence(const string sentence) {
        kb.push_back(Sentence(sentence));
    }

    friend ostream& operator<<(ostream &out, const KnowledgeBase& e) {
        cout << "Knowledge Base:" << endl;
        for (const auto& se: e.kb) {
            out << se << endl;
        }
        return out;
    }

    bool query(const Predicate& goal) {
        vector<Unification> unifs;
        goalOrigin = goal;
        stdID = 0;
        visited.clear();
        
        unifs = backChainOr(goal, Unification());
        cout << "Final Unifications: " << unifs << endl;
        return !unifs.empty();
    }
private:
    vector<Unification> backChainOr(const Predicate& goal, const Unification& theta) {
        vector<Unification> ret;
        //cout << goal.str() << endl;
        if (goal.allConst()) {      //Check loop
            string s = goal.str();
            if (visited.count(s) > 0) {
                return ret;
            }
            visited.insert(s);
        }
        for (auto e: kb) {
            e.standardize(stdID++);
            Predicate right = e.getRight();
            vector<Predicate> left = e.getLeft();

            if (goal.match(right)) {
                Unification tmpTheta = Unification::unify(right.getArgs(), goal.getArgs(), theta);
                
                vector<Unification> thetaAnd = backChainAnd(left, tmpTheta);
                for (const auto& theta1: thetaAnd) {
                    if (!theta1.fail()) {
                        ret.push_back(theta1);
                    }
                }
            }
        }
        if (goal.allConst()) {      //Check loop
            string s = goal.str();
            visited.erase(s);
        }
        return ret;
    }
    vector<Unification> backChainAnd(const vector<Predicate>& goals, const Unification& theta) {
        if (theta.fail()) {
            return {Unification(true)};
        }
        vector<Unification> ret;
        if (goals.empty()) {
            ret.push_back(theta);
        } else {
            Predicate first = goals[0].substitute(theta);
            
            vector<Predicate> rest(goals.begin() + 1, goals.end());
            
            vector<Unification> orTmp = backChainOr(first, theta);
            for (const auto& theta1: orTmp) {
                vector<Unification> andTmp = backChainAnd(rest, theta1);
                for (const auto& theta2: andTmp) {
                    if (!theta2.fail()) {
                        ret.push_back(theta2);
                    }
                }
            }
        }
        return ret;
    }
};

int main(int argc, char* argv[]) {
    string fileName = "input.txt";
    if (argc == 3 && string(argv[1]) == "-i") {
        fileName = argv[2];
    }
    ifstream fin(fileName);
    ofstream fou("output.txt");

    int n, m;
    vector<Predicate> queries;
    KnowledgeBase KB;
    string s;

    fin >> n;
    getline(fin, s);
    for (int i = 0; i < n; ++i) {
        getline(fin, s);
        queries.push_back(s);
    }

    fin >> m;
    getline(fin, s);
    for (int i = 0; i < m; ++i) {
        getline(fin, s);
        KB.addSentence(s);
    }
    
    fin.close();

    for (const auto& e: queries) {
        cout << e << endl;
    }
    cout << "============" << endl;
    
    cout << KB;
    cout << "============" << endl;

    for (const auto& e: queries) {
        fou << (KB.query(e)? "TRUE": "FALSE") << endl;
    }

    fou.close();
    
    return 0;
}