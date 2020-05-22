import copy
import time


class Predicate:

    # constructor
    def __init__(self, name, arguments, negation):
        self.name = name
        self.arguments = arguments
        self.negation = negation

    def __repr__(self):
        if self.negation:
            st = "~"
        else:
            st = ""
        st = st + self.name + "("
        for a in range(len(self.arguments)):
            if a == 0:
                st = st + str(self.arguments[a])
            else:
                st = st + "," + str(self.arguments[a])
        st = st + ")"
        return st

    def __eq__(self, other):
        return self.name == other.name and self.arguments == other.arguments and self.negation == other.negation

    def __ne__(self, other):
        return self.name != other.name

    def __cmp__(self, other):
        return self.name == other.name

    def __hash__(self):
        return hash((self.name, self.negation))

    def compound(self):
        if not isinstance(self, list):
            return len(self.name) >= 1 and self.arguments

    def has_constants(self):
        for literal in self.arguments:
            if not literal.islower():
                return True

    def is_equal(self, other):
        for p1 in range(len(self.arguments)):
            if not self.arguments[p1].islower() and not other.arguments[p1].islower():
                if self.arguments[p1] != other.arguments[p1]:
                    return False
        return True


class Sentence:
    st = ""
    valid = False

    # constructor
    def __init__(self, premises, count):
        self.premises = premises
        self.count = count
        for pr in range(len(self.premises)):
            if pr != 0 and pr != len(self.premises):
                self.st = self.st + " v "
            self.st = self.st + str(self.premises[pr])

    def __repr__(self):
        return self.st

    def __eq__(self, other):
        return self.st == other.st

    def __ne__(self, other):
        return self.st != other.st

    def __cmp__(self, other):
        return self.st == other.st

    def __hash__(self):
        return hash(self.premises[0])

    def standardize(self, variable_counter):
        variable_mapping = {}
        standardized_premises = []
        for p in self.premises:
            updated_args = []
            for var in range(len(p.arguments)):
                if p.arguments[var].islower() and p.arguments[var]in variable_mapping.keys():
                    p.arguments[var] = variable_mapping[p.arguments[var]]
                elif p.arguments[var].islower():
                    variable_mapping[p.arguments[var]] = "v" + str(variable_counter)
                    variable_counter = variable_counter + 1
                    p.arguments[var] = variable_mapping[p.arguments[var]]
                updated_args.append(p.arguments[var])
            pred = Predicate(p.name, updated_args, p.negation)
            standardized_premises.append(pred)
        return Sentence(standardized_premises, 0), variable_counter

    def form_clause(self, other, theta):
        index1 = -1
        index2 = -1
        prem = []
        s1 = copy.deepcopy(self)
        s2 = copy.deepcopy(other)

        for m in theta.keys():
            val = theta[m]
            for predicate in s1.premises:
                for a in range(len(predicate.arguments)):
                    if predicate.arguments[a] == m:
                        predicate.arguments[a] = val

            for predicate in s2.premises:
                for a in range(len(predicate.arguments)):
                    if predicate.arguments[a] == m:
                        predicate.arguments[a] = val

        for c1 in range(len(s1.premises)):
            for c2 in range(len(s2.premises)):
                if s1.premises[c1].name == s2.premises[c2].name and s1.premises[c1].negation != s2.premises[c2].negation and s1.premises[c1].arguments == s2.premises[c2].arguments:
                    index1 = c1
                    index2 = c2
                    break
            if index1 != -1 and index2 != -1:
                break
        if index1 != -1 and index2 != -1:
            s2.premises.pop(index2)
            s1.premises.pop(index1)

        for c1 in range(len(s1.premises)):
            prem.append(s1.premises[c1])

        for c2 in range(len(s2.premises)):
            prem.append(s2.premises[c2])

        statement = Sentence(prem, 0)
        return statement

    def reset_sentence_count(self, sentences):
        for s in sentences:
            s.count = 0

    def sentence_use_count(self, sentences):
        for s in sentences:
            if self.count > s.count:
                return False
        return True

    def solve_query(self, other, variable_counter):
        global start_time
        index1 = -1
        index2 = -1
        if (time.time() - start_time) >= time_required:
            self.valid = False
            return self.valid
        u = Unify()
        theta = {}
        for c1 in range(len(self.premises)):
            for c2 in range(len(other.premises)):
                if self.premises[c1].name == other.premises[c2].name and self.premises[c1].negation != other.premises[c2].negation:
                    index1 = c1
                    index2 = c2
                    theta = u.unify(other.premises[index2], self.premises[index1], {})
                    if isinstance(theta, dict) and bool(theta):
                        break
            if isinstance(theta, dict) and bool(theta):
                break
        if isinstance(theta, dict):
            c = other.form_clause(self, theta)
            c, variable_counter = c.standardize(variable_counter)
            if not c.premises:
                self.valid = True
                return self.valid

            for e in c.premises:
                count_of_predicate = 0
                count_of_equal_predicate = 0
                if e.has_constants():
                    predicate_name = e.name
                    for lst in predicate_indexing[predicate_name]:
                        if lst.negation != e.negation:
                            count_of_predicate = count_of_predicate + 1
                            if lst.has_constants():
                                if not e.is_equal(lst):
                                    count_of_equal_predicate = count_of_equal_predicate + 1
                    if count_of_equal_predicate == count_of_predicate:
                        return False

            for e in c.premises:
                x = e.name
                ng = e.negation
                if x in predicate_indexing.keys():
                    st = predicate_indexing[x]
                    st.add(e)
                    predicate_indexing[x] = st
                else:
                    st = set()
                    st.add(e)
                    predicate_indexing[x] = st
                if e in sentence_indexing.keys():
                    st = sentence_indexing[e]
                    st.add(c)
                    sentence_indexing[e] = st
                else:
                    st = set()
                    st.add(c)
                    sentence_indexing[e] = st

                set_of_sentences = set()
                for lst in predicate_indexing[x]:
                    if lst.negation != ng:
                        for lst_sent in sentence_indexing[lst]:
                            set_of_sentences.add(lst_sent)

                for lst in predicate_indexing[x].copy():
                    if lst.negation != ng:
                        for lst_sent in sentence_indexing[lst].copy():
                            used = lst_sent.sentence_use_count(set_of_sentences)
                            if used:
                                lst_sent.count = lst_sent.count + 1
                                self.valid = c.solve_query(lst_sent, variable_counter)
                                if self.valid:
                                    return self.valid
                    if self.valid:
                        return self.valid
            return self.valid
        else:
            self.valid = False
            return self.valid


class Unify:

    def unify(self, x, y, theta):
        if theta is False:
            return False
        elif x == y:
            return theta
        elif isinstance(x, str) and self.variable(x):
            return self.unify_var(x, y, theta)
        elif isinstance(y, str) and self.variable(y):
            return self.unify_var(y, x, theta)
        elif isinstance(x, list) and isinstance(y, list):
            x_copy = copy.deepcopy(x)
            y_copy = copy.deepcopy(y)
            x_first = x_copy.pop(0)
            y_first = y_copy.pop(0)
            return self.unify(x_copy, y_copy, self.unify(x_first, y_first, theta))
        elif not isinstance(x, str) and not isinstance(y, str) and self.compound(x) and self.compound(y):
            return self.unify(x.arguments, y.arguments, self.unify(x.name, y.name, theta))
        else:
            return False

    def variable(self, x):
        if not isinstance(x, list):
            return x.islower()

    def compound(self, x):
        return len(x.name) >= 1 and x.arguments

    def unify_var(self, var, x, theta):
        if var in theta:
            return self.unify(theta[var], x, theta)
        elif x in theta:
            return self.unify(var, theta[x], theta)
        else:
            theta[var] = x
            return theta


predicates = set()
sentences = set()
predicate_indexing_original = {}
sentence_indexing_original = {}
sentence_indexing = {}
predicate_indexing = {}
variable_counter = 1

# open the input file to read the input
input_file = open("input.txt")

queries = []
knowledge_base = []

# number of queries
no_of_queries = input_file.readline().strip()

# store all queries in a set
for i in range(int(no_of_queries)):
    q = input_file.readline().strip()
    queries.append(q)

# number of sentences in KB
no_of_sentences = input_file.readline().strip()

# store all sentences in KB
for i in range(int(no_of_sentences)):
    kb = input_file.readline().strip()
    knowledge_base.append(kb)

for i in range(len(knowledge_base)):
    pre = []
    if knowledge_base[i].__contains__('=>'):
        k = knowledge_base[i].split('=> ')[1]
        n = k[k.find("~")+1: k.find('(')]
        arg = k[k.find("(")+1:k.find(")")].split(',')
        neg = k.__contains__('~')
        p = Predicate(n, arg, neg)
        predicates.add(p)
        premise = knowledge_base[i].split('=>')[0].split('& ')
        for j in range(len(premise)):
            n = premise[j][premise[j].find('~')+1: premise[j].find('(')]
            arg = premise[j][premise[j].find("(")+1: premise[j].find(")")].split(',')
            neg = not(premise[j].__contains__('~'))
            p1 = Predicate(n, arg, neg)
            pre.append(p1)
            predicates.add(p1)
        pre.append(p)
        s = Sentence(pre, 0)
        s, variable_counter = s.standardize(variable_counter)
        sentences.add(s)
    else:
        n = knowledge_base[i][knowledge_base[i].find('~')+1: knowledge_base[i].find('(')]
        arg = knowledge_base[i][knowledge_base[i].find("(")+1: knowledge_base[i].find(")")].split(',')
        neg = knowledge_base[i].__contains__('~')
        p = Predicate(n, arg, neg)
        predicates.add(p)
        s = Sentence([p], 0)
        s, variable_counter = s.standardize(variable_counter)
        sentences.add(s)

for p in predicates:
    s = set()
    sen = set()
    if p.name in predicate_indexing_original.keys():
        s = predicate_indexing_original[p.name]
        s.add(p)
        predicate_indexing_original[p.name] = s
    else:
        s.add(p)
        predicate_indexing_original[p.name] = s

    for sent in sentences:
        if p in sent.premises:
            sen.add(sent)
    sentence_indexing_original[p] = sen

# handle infinite loop cases
time_required = 0.3
KB_length = len(sentence_indexing_original)
max_depth = 2*len(sentence_indexing_original)

output_file = open("output.txt", 'w')

results = []

# resolve each query
for q in queries:
    predicate_indexing = copy.deepcopy(predicate_indexing_original)
    sentence_indexing = copy.deepcopy(sentence_indexing_original)
    found = False
    result = False
    sent_set = set()
    pred_set = set()
    if q.__contains__('~'):
        q_name = q[q.find('~')+1: q.find('(')]
        q_neg = False
    else:
        q_name = q.split('(')[0]
        q_neg = True
    q_args = q[q.find('(')+1: q.find(')')].split(',')
    query_predicate = Predicate(q_name, q_args, q_neg)
    s1 = Sentence([query_predicate], 0)
    sent_set.add(s1)
    sentence_indexing[query_predicate] = sent_set
    if q_name in predicate_indexing.keys():
        pred_set = predicate_indexing[q_name]
        pred_set.add(query_predicate)
    else:
        results.append("FALSE")
        continue
    for p in predicate_indexing[q_name].copy():
        if p.negation != q_neg:
            found = True
            for sent in sentence_indexing[p].copy():
                sent.reset_sentence_count(sentence_indexing[p].copy())
                used = sent.sentence_use_count(sentence_indexing[p])
                if used:
                    sent.count = sent.count + 1
                    s2 = sent
                    start_time = time.time()
                    result = s1.solve_query(s2, variable_counter)
                    if result:
                        break
        if result:
            break
        predicate_indexing = copy.deepcopy(predicate_indexing_original)
        sentence_indexing = copy.deepcopy(sentence_indexing_original)
        if q_name in predicate_indexing.keys():
            pred_set = predicate_indexing[q_name]
            pred_set.add(query_predicate)
        sentence_indexing[query_predicate] = sent_set
    if result:
        results.append("TRUE")
    else:
        results.append("FALSE")
    sentence_indexing.pop(query_predicate)
    pred_set.remove(query_predicate)

for r in range(len(results)):
    if r != len(results) - 1:
        output_file.write(results[r] + "\n")
    else:
        output_file.write(results[r])

output_file.close()
