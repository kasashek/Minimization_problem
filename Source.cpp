#include <iostream>
#include <vector>
#include <string>
#include <map>
#include <variant>
#include <algorithm>
#include <queue>
using expr_type = std::string; //тип выражения - гипотеза, аксиома, модус поненс или непонятно что

std::map<char, int> operations{
        {'-', 1},
        {'|', 2},
        {'&', 3},
        {'!', 4},
};

std::vector<std::string> AXIOMS{
        "A->(B->A)",
        "(A->B)->(A->B->C)->(A->C)",
        "A->B->A&B",
        "A&B->A",
        "A&B->B",
        "A->A|B",
        "B->A|B",
        "(A->C)->(B->C)->(A|B->C)",
        "(A->B)->(A->!B)->!A",
        "!!A->A"
};


std::string deleteSpaces(std::string str) {
    for (int i = 0; i < str.length(); i++) {
        if (str[i] == ' ' || str[i] == '\r') {
            str.erase(i, 1);
            i--;
        }
    }
    return str;
}

//сюда подаётся первая строка доказательства уже без пробелов
//данная функция заполняет вектор гипотез
void getHypotheses(std::vector<std::string>& hyps, std::string& firstStringOfEv) {
    if (firstStringOfEv[0] == '|' && firstStringOfEv[1] == '-')
        return;
    else {
        std::string hypsSeq;
        size_t k = 0;
        while ((firstStringOfEv[k] != '|' || firstStringOfEv[k + 1] != '-') && k < firstStringOfEv.size() - 1) {
            hypsSeq += firstStringOfEv[k];
            k++;
        }
        hyps.push_back("");
        size_t j = 0;
        for (size_t i = 0; i < hypsSeq.length(); ++i) {
            if (hypsSeq[i] != ',')
                hyps[j] += hypsSeq[i];
            else {
                hyps.push_back("");
                ++j;
            }
        }
    }
}

//сюда подаётся первая строка доказательства уже без пробелов
//данная функция позволяет запомнить утверждение, которое мы доказываем
void getProvenStatement(std::string& toProve, std::string& firstStringOfEv) {
    for (size_t i = 0; i < firstStringOfEv.size(); ++i) {
        if (firstStringOfEv[i] == '|') {
            for (size_t j = i + 2; j < firstStringOfEv.size(); ++j) {
                toProve += firstStringOfEv[j];
            }
            break;
        }
    }
}

//берём доказательство (уже без пробелов) и проверяем каждую строку на то, гипотеза ли это
//? может означать модус поненс или просто непонятно что (то есть некорректность)
void hypothesisChecker(std::vector<std::string>& hyps, std::vector<std::string>& evStrings, std::vector<expr_type>& exprTypes) {
    for (size_t i = 0; i < evStrings.size(); ++i) {
        for (size_t j = 0; j < hyps.size(); ++j) {
            if (evStrings[i] == hyps[j]) {
                exprTypes[i] = "Hypothesis " + std::to_string(j + 1);
                break;
            }
        }
    }
}

//получение индекса самой приоритетной операции
int check_oper(std::string sent) {
    int k = -1, prior = 5, depth = 0;
    std::map<char, int> opers = {
            {'-', 1},
            {'|', 2},
            {'&', 3},
            {'!', 4}
    };
    for (int i = 0; i < sent.size(); i++) {
        if (sent[i] == '(') {
            depth++;
            continue;
        }
        else if (sent[i] == ')') {
            depth--;
            continue;
        }
        else if (opers.count(sent[i]) && opers.find(sent[i])->second < prior && depth == 0 && (opers.find(sent[i])->second == 1 ||
            opers.find(sent[i])->second == 4)) {
            prior = opers.find(sent[i])->second;
            k = i;
            if (prior == 1) {
                return k;
            } // global minimum
        }
        else if (opers.count(sent[i]) && opers.find(sent[i])->second <= prior && depth == 0 &&
            2 <= opers.find(sent[i])->second && opers.find(sent[i])->second <= 3) {
            prior = opers.find(sent[i])->second;
            k = i;
        }
    }
    return k;
}

//получение дерева разбора аксиомы
void parse_Axiom(std::string sent, std::vector<std::string>& Tree, int v) {
    int i = check_oper(sent); // analysis of the operation
    if (i == -1) {
        if (sent[0] == '(') {
            //ans[v] = "()";
            parse_Axiom(sent.substr(1, sent.size() - 2), Tree, v);//parsing brackets
        }
        else {
            Tree[v] = sent; // adding variables
        }
    }
    else if (sent[i] == '-') {
        Tree[v] = sent.substr(i, 2); // operation
        parse_Axiom(sent.substr(0, i), Tree, 2 * v + 1); // analysis left side
        parse_Axiom(sent.substr(i + 2, sent.size() - 1), Tree, 2 * v + 2); //analysis right side
    }
    else if (sent[i] == '!') {
        Tree[v] = sent.substr(i, 1);
        parse_Axiom(sent.substr(i + 1, sent.size() - 1), Tree, 2 * v + 1);
    }
    else {
        Tree[v] = sent.substr(i, 1);
        parse_Axiom(sent.substr(0, i), Tree, 2 * v + 1);
        parse_Axiom(sent.substr(i + 1, sent.size() - 1), Tree, 2 * v + 2);
    }
}

//получение дерева разбора выражения
void parse_Term(std::string sent, std::vector<std::string>& Tree, std::vector<std::string>& Operation,
    int v, std::vector<std::string>& Axiom_Tree) {
    int i = check_oper(sent); // analysis of the operation
    if (Axiom_Tree[v] == "-1") {
        return;
    }
    if (i == -1) {
        if (sent[0] == '(') {
            //ans[v] = "()";
            parse_Term(sent.substr(1, sent.size() - 2), Tree, Operation, v, Axiom_Tree);//parsing brackets
        }
        else {
            Operation[v] = sent;
            Tree[v] = sent; // adding variables
        }
    }
    else if (sent[i] == '-') {
        Operation[v] = sent.substr(i, 2);
        Tree[v] = sent; // operation
        parse_Term(sent.substr(0, i), Tree, Operation, 2 * v + 1, Axiom_Tree); // analysis left side
        parse_Term(sent.substr(i + 2, sent.size() - 1), Tree, Operation, 2 * v + 2, Axiom_Tree); //analysis right side
    }
    else if (sent[i] == '!') {
        Operation[v] = sent.substr(i, 1);
        Tree[v] = sent;
        parse_Term(sent.substr(i + 1, sent.size() - 1), Tree, Operation, 2 * v + 1, Axiom_Tree);
    }
    else {
        Operation[v] = sent.substr(i, 1);
        Tree[v] = sent;
        parse_Term(sent.substr(0, i), Tree, Operation, 2 * v + 1, Axiom_Tree);
        parse_Term(sent.substr(i + 1, sent.size() - 1), Tree, Operation, 2 * v + 2, Axiom_Tree);
    }
}

//проверка, является ли выражение аксиомой
bool Is_Axioms(std::string& Term, std::string& Axiom) {
    std::vector<std::string> Term_Tree((1 << 10), "-1"), Term_operation((1 << 10), "-1");
    std::vector<std::string> Axiom_Tree((1 << 10), "-1");
    parse_Axiom(deleteSpaces(Axiom), Axiom_Tree, 0);
    parse_Term(deleteSpaces(Term), Term_Tree, Term_operation, 0, Axiom_Tree);
    bool tmp = true;
    int cnt = 0;
    std::string A, B, C;
    A = B = C = "-1";
    for (size_t i = 0; i < (1 << 10); ++i) {
        //std::cout << "i: " << i << "  " << Term_Tree[i] << " " << Axiom_Tree[i] << std::endl;
        if (Axiom_Tree[i] != "A" && Axiom_Tree[i] != "B" && Axiom_Tree[i] != "C") {
            if (Term_operation[i] != Axiom_Tree[i])
                tmp = false;
        }
        else if (Axiom_Tree[i] == "A") {
                    if (A == "-1") {
                        A = Term_Tree[i];
                        if (Term_Tree[i] == "-1")
                            tmp = false;
                    }
                    else {
                        if (A != Term_Tree[i]) {
                            tmp = false;
                        }
                    }
                }
                else if (Axiom_Tree[i] == "B") {
                    if (B == "-1") {
                        B = Term_Tree[i];
                        if (Term_Tree[i] == "-1")
                            tmp = false;
                    }
                    else {
                        if (B != Term_Tree[i]) {
                            tmp = false;
                        }
                    }
                }
                else if (Axiom_Tree[i] == "C") {
                    if (C == "-1") {
                        C = Term_Tree[i];
                        if (Term_Tree[i] == "-1")
                            tmp = false;
                    }
                    else {
                        if (C != Term_Tree[i]) {
                            tmp = false;
                        }
                    }
                }
    }
    return tmp;
}

//инициализация аксиом в векторе типов выражений
void initializeAxioms(std::vector<std::string>& ev, std::vector<std::string>& exprTypes) {
    int ans = 0;
    for (size_t i = 1; i < ev.size(); ++i) {
        for (size_t j = 0; j < AXIOMS.size(); ++j) {
            if (!ans)
                ans = Is_Axioms(ev[i], AXIOMS[j]) * (j + 1);
        }
        if (ans != 0) {
            exprTypes[i] = "Ax. sch. " + std::to_string(ans);
        }
        ans = 0;
    }
}


//не костыль, а фича
void parse_Expr(std::string sent, std::vector<std::string>& Tree, int v, std::vector<std::string>& Axiom_Tree) {
    int i = check_oper(sent); // analysis of the operation
    if (Axiom_Tree[v] == "-1") {
        return;
    }
    if (v > 2) {
        return;
    }
    else if (v > 0) {
        if (i == -1) {
            if (sent[0] == '(') {
                //ans[v] = "()";
                parse_Expr(sent.substr(1, sent.size() - 2), Tree, v, Axiom_Tree);//parsing brackets
            }
            else {
                Tree[v] = sent; // adding variables
            }
        }
        if (Tree[v] == "-1") {
            Tree[v] = sent;
        }
        return;
    }
    //случай v == 0
    if (i == -1) {
        if (sent[0] == '(') {
            //ans[v] = "()";
            parse_Expr(sent.substr(1, sent.size() - 2), Tree, v, Axiom_Tree);//parsing brackets
        }
        else {
            Tree[v] = sent; // adding variables
        }
    }
    else if (sent[i] == '-') {
        Tree[v] = sent.substr(i, 2); // operation
        parse_Expr(sent.substr(0, i), Tree, 2 * v + 1, Axiom_Tree); // analysis left side
        parse_Expr(sent.substr(i + 2, sent.size() - 1), Tree, 2 * v + 2, Axiom_Tree); //analysis right side
    }
    else if (sent[i] == '!') {
        Tree[v] = sent;
        parse_Expr(sent.substr(i + 1, sent.size() - 1), Tree, 2 * v + 1, Axiom_Tree);
    }
    else {
        Tree[v] = sent;
        parse_Expr(sent.substr(0, i), Tree, 2 * v + 1, Axiom_Tree);
        parse_Expr(sent.substr(i + 1, sent.size() - 1), Tree, 2 * v + 2, Axiom_Tree);
    }
}

//сравнение для проверки на МП
//на входе выражение A->B и B
std::string compareTerms(std::string& Term1, std::string& Term2) {
    std::vector<std::string> Term_Tree((1 << 10), "-1");
    std::vector<std::string> Axiom_Tree((1 << 10), "-1");
    Axiom_Tree[0] = "->";
    Axiom_Tree[1] = "A";
    Axiom_Tree[2] = "B";
    parse_Expr(deleteSpaces(Term1), Term_Tree, 0, Axiom_Tree);
    bool tmp = true;
    std::string A, B;
    A = B = "-1";
    A = Term_Tree[1];
    B = Term_Tree[2];
    if (B == Term2 && tmp)
        return A;
    else
        return "-1";
}

//проверка на М.П., заполнение вектора М.П. и вектора пар использованных строк
void getModusPonens(std::vector<std::string>& ev, std::vector<std::string>& exprTypes, 
                    std::vector<std::string>& mp, std::vector<std::vector<std::pair<size_t, size_t>>>& usedInMP) {
    for (size_t i = 1; i < ev.size(); ++i) {
        if (exprTypes[i] == "?") {
            usedInMP[i].resize(1);
            //j это индекс аксиомы
            for (size_t j = 1; j < i; ++j) {
                std::string A = compareTerms(ev[j], ev[i]);
                //k это индекс гипотезы
                for (size_t k = 1; k < i; ++k) {
                    if (ev[k] == A) {
                        exprTypes[i] = "M.P. " + std::to_string(j) + ", " + std::to_string(k);
                        usedInMP[i].push_back({ j, k });
                        mp.push_back(ev[i]);
                    }
                }
            }
        }
    }
}

//спуск по доказательству какого-либо факта(так как рекурсивный)
int finder_Tree(int ind, std::vector<std::string>& exprTypes, 
                std::vector<std::vector<std::pair<size_t, size_t>>>& usedInMP,
                std::vector<std::pair<int, int>>& sons) {
    int d = 1e6;
    if (exprTypes[ind][0] != 'M') {
        return 1;
    }
    if (exprTypes[ind][0] == 'M') {
        for (size_t i = 1; i < usedInMP[ind].size(); ++i) {
            int ind1, ind2;
            ind1 = usedInMP[ind][i].first;
            ind2 = usedInMP[ind][i].second;
            int l, r;
            l = finder_Tree(ind1, exprTypes, usedInMP, sons);
            r = finder_Tree(ind2, exprTypes, usedInMP, sons);
            if (i == 1) {
                sons[ind] = { ind1, ind2 };
                d = l + r + 1;
            }
            else if (d > l + r + 1) {
                sons[ind] = { ind1, ind2 };
                d = l + r + 1;
            }
        }
    }
    return d;
}

//восстановление минимизированного дерева
void maker_Tree(int ind, std::vector<int>& used, std::vector<std::pair<int, int>>& sons) {
    if (ind == -1)
        return;
    used[ind] = 1;
    if (sons[ind].first != -1)
        maker_Tree(sons[ind].first, used, sons);
    if (sons[ind].second != -1)
        maker_Tree(sons[ind].second, used, sons);
    return;
}

//преобразование строчек в формат, нужный для ответа
std::string unparse(std::string sent) {
    std::string answer;
    int i = check_oper(sent); // analysis of the operation
    if (i == -1) {
        if (sent[0] == '(') {
            answer = unparse(sent.substr(1, sent.size() - 2));//parsing brackets
        }
        else {
            answer += sent; // adding variables
        }
    }
    else if (sent[i] == '-') {
        std::string left, right;
        left = unparse(sent.substr(0, i)); // analysis left side
        right = unparse(sent.substr(i + 2, sent.size() - 1)); //analysis right side
        answer = "(" + left + " -> " + right + ")";
    }
    else if (sent[i] == '!') {        
        answer = "!" + unparse(sent.substr(1, sent.size() - 1));
    }
    else {
        std::string left, right;
        left = unparse(sent.substr(0, i));
        right = unparse(sent.substr(i + 1, sent.size() - 1));
        answer = "(" + left + " " + sent[i] + " " + right + ")";
    }
    return answer;
}

//минимизация доказательства
void minimize(std::vector<std::string>& ev, std::vector<std::string>& exprTypes, 
              std::vector<std::string>& mp, std::vector<std::vector<std::pair<size_t, size_t>>>& usedInMP) {
    //сама минимизация
    std::vector<int> used(ev.size(), 0);
    std::vector<std::pair<int, int>> sons(ev.size(), {-1, -1});
    int d = finder_Tree(ev.size() - 1, exprTypes, usedInMP, sons);
    maker_Tree(ev.size() - 1, used, sons);
    
    //новое минимизированное доказательство
    std::vector<std::string> evidence;
    evidence.push_back(ev[0]);
    for (size_t i = 1; i < ev.size(); ++i) {
        if (used[i] == 1)
            evidence.push_back(ev[i]);
    }
    std::vector<std::string> hypotheses;
    getHypotheses(hypotheses, evidence[0]);
    //вектор типов выражений
    std::vector<expr_type> expressionTypes(evidence.size(), "?");
    expressionTypes[0] = "";
    //запоминание доказуемого утверждения
    std::string toProve = "";
    getProvenStatement(toProve, evidence[0]);
    //проверка на принадежность к гипотезам
    hypothesisChecker(hypotheses, evidence, expressionTypes);
    //проверка на принадлежность к аксиомам
    initializeAxioms(evidence, expressionTypes);
    //ищем М.П.
    std::vector<std::string> MP;
    std::vector<std::vector<std::pair<size_t, size_t>>> usedInMP2(evidence.size());
    getModusPonens(evidence, expressionTypes, MP, usedInMP2);
    std::string aft = "";
    std::vector<std::string> bef;
    size_t i = 0;
    bef.push_back("");
    for (i = 0; i < evidence[0].size(); ++i) {
        if (evidence[0][i] == '|' && evidence[0][i + 1] == '-')
            break;
        if (evidence[0][i] == ',')
            bef.push_back("");
        else bef[bef.size() - 1] += evidence[0][i];
    }
    i += 2;
    for (i; i < evidence[0].size(); ++i) {
         aft += evidence[0][i];
    }
    for (i = 0; i < bef.size(); ++i) {
        std::cout << unparse(bef[i]);
        if (i != bef.size() - 1)
            std::cout << ", ";
    }
    if (bef.size() == 1 && bef[bef.size() - 1] == "")
        std::cout << "|- " << unparse(aft) << std::endl;
    else
        std::cout << " |- " << unparse(aft) << std::endl;
    for (i = 1; i < evidence.size(); ++i) {
        std::cout << "[" << i << ". " << expressionTypes[i] << "] " << unparse(evidence[i]) << std::endl;
    }
}



///проверка на корректность доказательства
bool correctnessChecker(std::vector<std::string>& ev, std::string& toProve, std::vector<std::string>& exprTypes) {
    //последняя строка не является доказываемым утверждением
    if (ev[ev.size() - 1] != toProve) {
        return false;
    }
    //есть невыведенные выражения
    for (size_t i = 0; i < exprTypes.size(); ++i)
        if (exprTypes[i] == "?")
            return false;
    return true;
}


/*
A->B, !B |- !A
A->B
!B
!B -> A -> !B
A -> !B
(A -> B) -> (A -> !B) -> !A
(A -> !B) -> !A
!A
 */

 /*
 A, A->X, A->B, B->X |- X
 A
 A->X
 A->B
 B
 B->X
 X
 */

int main() {
    std::vector<std::string> evidence;
    std::string str;
    //ввод неизвестного числа строк
    while (getline(std::cin, str)) {
        if (str.empty())
            break;
        evidence.push_back(str);
    }
    //удаление пробелов
    for (size_t i = 0; i < evidence.size(); ++i) {
        evidence[i] = deleteSpaces(evidence[i]);
    }
    
    //заполнение вектора гипотез
    std::vector<std::string> hypotheses;
    getHypotheses(hypotheses, evidence[0]);
    //вектор типов выражений
    std::vector<expr_type> expressionTypes(evidence.size(), "?");
    expressionTypes[0] = "";
    //запоминание доказуемого утверждения
    std::string toProve = "";
    getProvenStatement(toProve, evidence[0]);
    //проверка на принадежность к гипотезам
    hypothesisChecker(hypotheses, evidence, expressionTypes);
    //проверка на принадлежность к аксиомам
    initializeAxioms(evidence, expressionTypes);
    //ищем М.П.
    std::vector<std::string> MP;
    std::vector<std::vector<std::pair<size_t, size_t>>> usedInMP(evidence.size());
    getModusPonens(evidence, expressionTypes, MP, usedInMP);
    if (!correctnessChecker(evidence, toProve, expressionTypes)) {
        std::cout << "Proof is incorrect" << std::endl;
        return 0;
    }
    minimize(evidence, expressionTypes, MP, usedInMP);
    return 0;
}