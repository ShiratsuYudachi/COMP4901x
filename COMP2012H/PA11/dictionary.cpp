#include <vector>
#include <iostream>

#include "dictionary.h"

using namespace std;

// this function will not be used in any way. For C++, templates are usually defined in header files. 
// However, for ZINC grading, we separate it into different files. So we need to use this 'trick' to
// instantiate the temnplate.
void compiler_trick_useless_function(){
    Dictionary d{""};
    lambda_for_main_cpp ct;
    d.foreach(ct);
}

int Dictionary::character_to_index(const char& ch){
    return ch - 97;
}

char Dictionary::index_to_character(const int& idx){
    return (char) (idx + 97);
}

const string& Dictionary::get_name() const{
    return name;
}

void Dictionary::set_name(const string& name){
    this->name = name;
}

Dictionary::Dictionary(const string& name)
    : name(name) 
{
    root = new Node;
}

Dictionary::~Dictionary(){
    delete root;
}

Dictionary::Dictionary(Dictionary&& d){
    root = d.root;
    d.root = nullptr;
}

Dictionary& Dictionary::operator=(Dictionary&& d){
    delete root;
    root = d.root;
    d.root = nullptr;

    return *this;
}

ostream& operator<<(ostream& o, Node* n){
    o << (*n);
    return o;
}

ostream& operator<<(ostream& o, const Node& n){
    o << " (" << n.meaning.type << ") " << n.meaning.meaning << " ";
    return o;
}

/**
 * TODO - Constructor for deep copy of dictionary.
*/
Dictionary::Dictionary(const Dictionary& d){
    root = new Node;
    d.foreach([&] (Node* node, vector<int>& key) mutable {
        Node* curr = root;
        for (vector<int>::const_iterator itr = key.begin(); itr + 1 < key.end(); itr++) {
            curr = (*curr)[*itr];
        }
        Node* n = new Node;
        n->get_parent() = curr;
        curr->set_child(key.back(), n);
        n->meaning.meaning = node->meaning.meaning;
        n->meaning.type = node->meaning.type;
    });
}

/**
 * TODO - Assignment operator for deep copy of dictionary.
*/
Dictionary& Dictionary::operator=(const Dictionary& d){
    if (this == &d) return *this;
    delete root;
    root = new Node;
    d.foreach([&] (Node* node, vector<int>& key) mutable {
        Node* curr = root;
        for (vector<int>::const_iterator itr = key.begin(); itr + 1 < key.end(); itr++) {
            curr = (*curr)[*itr];
        }
        Node* n = new Node;
        n->get_parent() = curr;
        curr->set_child(key.back(), n);
        n->meaning.meaning = node->meaning.meaning;
        n->meaning.type = node->meaning.type;
    });
    return *this;
}

/**
 * TODO - Adds a node with the given key string, which is terminated with '\0'.
 * You should assume the key consists of lowercase letters only.
 * Do not delete the pointer.
*/
Node* Dictionary::add_node(const char* key){
    Node* curr = root;
    for (int i = 0; key[i] != '\0'; i++) {
        Node* next = (*curr)[character_to_index(key[i])];
        if (next == nullptr) {
            next = new Node;
            next->get_parent() = curr;
            curr->set_child(character_to_index(key[i]), next);
        }
        curr = next;
    }
    return curr;
}

/**
 * TODO - Shorthand for add_node.
*/
Node* Dictionary::operator+=(const char* key){
    return add_node(key);
}

/**
 * TODO - Removes all nodes starting with the given key string, which is terminated with '\0'.
 * You should assume the key consists of lowercase letters only.
 * Do not delete the pointer const char* key (of course you should clean up the nodes that are removed).
*/
void Dictionary::remove_node(const char* key){
    Node* curr = root;
    int i = 0;
    while (true) {
        Node* next = (*curr)[character_to_index(key[i])];
        if (next == nullptr) return;
        if (key[i + 1] == '\0') {
            delete next;
            curr->set_child(character_to_index(key[i]), nullptr);
            return;
        }
        curr = next;
        i++;
    }
}

/**
 * TODO - Shorthand for remove_node.
*/
void Dictionary::operator-=(const char* key){
    remove_node(key);
}

/**
 * TODO - Finds a node with the given key string, which is terminated with '\0'.
 * Returns nullptr if no such node is found.
 * You should assume the key consists of lowercase letters only.
 * Do not delete the pointer.
*/
Node* Dictionary::find_node(const char* key) const{
    Node* curr = root;
    for (int i = 0; key[i] != '\0'; i++) {
        Node* next = (*curr)[character_to_index(key[i])];
        if (next == nullptr) return nullptr;
        curr = next;
    }
    return curr;
}

/**
 * TODO - A function to do pre-order traversal on the tree. The function accepts a lambda function as argument,
 * and then the lambda function would be called for every node in the tree (except the root node). 
 * The lambda function accepts two arguments, (Node* current_node, vector<int>& current_key).
 * For each node accessed via pre-order traversal (except root node), call the lambda function.
 * 
 * Of course current_node should be the pointer to the node accessed. current_key should contain
 * a list of integers which corresponds to the indices required to travel to current_node from
 * the root node. For more explanation see the webpage.
 * 
 * The lambda is not supposed to change the dictionary.
*/
template<typename T> void preorder(Node* curr, vector<int> key, T&& lambda) {
    for (int i = 0; i < 26; i++) {
        if (i > 0) key.pop_back();
        key.push_back(i);
        Node* next = (*curr)[i];
        if (next != nullptr) {
            lambda(next, key);
            preorder(next, key, lambda);
        }
    }
}

template<typename T> void Dictionary::foreach(T&& lambda) const{
    vector<int> key;
    preorder(root, key, lambda);
}

/**
 * TODO - Prints all the nodes in the dictionary, in depth first alphabetical order.
 * See the webpage description for more details.
*/
void Dictionary::print_all_elements(ostream& o) const{
    int count = 0;
    foreach([&] (Node* node, vector<int>& key) mutable {
        string keystr;
        for (vector<int>::const_iterator itr = key.begin(); itr < key.end(); itr++) {
            keystr.push_back(index_to_character(*itr));
        }
        count++;
        cout << keystr << node << "[" << count << "]\n";
    });
}

/**
 * TODO - Calls print_all_elements
*/
std::ostream& operator<<(std::ostream& o, const Dictionary& dict){
    dict.print_all_elements(o);
    return o;
}

/**
 * TODO - Prints all the words in the dictionary, such that the word type is equal to the given type,
 * in depth first alphabetical order. See the webpage description for more details.
*/
void Dictionary::print_elements_given_type(const char* type) const{
    int count = 0;
    foreach([&] (Node* node, vector<int>& key) mutable {
        if (node->meaning.meaning.empty()) return;
        if (type != nullptr && node->meaning.type.compare(type) != 0) return;
        string keystr;
        for (vector<int>::const_iterator itr = key.begin(); itr < key.end(); itr++) {
            keystr.push_back(index_to_character(*itr));
        }
        count++;
        cout << keystr << node << "[" << count << "]\n";
    });
}

/**
 * TODO - Merges with another dictionary. Creates a new dictionary,
 * and does not modify the contents of the original dictionaries.
 * For words that exists in both dictionary,
 * use the word definition in the dictionary this.
*/
Dictionary Dictionary::merge(const Dictionary& d2) const{
    Dictionary result(d2);
    Node* curr = result.root;
    int len = 0;
    foreach([&] (Node* node, vector<int>& key) mutable {
        while (key.size() <= len) {
            curr = &*(curr->get_parent());
            len--;
        }
        Node* n = (*curr)[key.back()];
        
        if (n == nullptr) {
            n = new Node;
            n->get_parent() = curr;
            curr->set_child(key.back(), n);
        }
        curr = n;
        len++;
        if (node->meaning.meaning.empty()) return;
        n->meaning.meaning = node->meaning.meaning;
        n->meaning.type = node->meaning.type;
    });
    return result;
}

/**
 * TODO - Merges with another dictionary. Moves the contents of d2
 * into a new dictionary. For words that exists in both dictionary,
 * use the word definition in the dictionary this.
*/
Dictionary Dictionary::merge(Dictionary&& d2) const{
    Dictionary result(move(d2));
    Node* curr = result.root;
    int len = 0;
    foreach([&] (Node* node, vector<int>& key) mutable {
        while (key.size() <= len) {
            curr = &*(curr->get_parent());
            len--;
        }
        Node* n = (*curr)[key.back()];
        
        if (n == nullptr) {
            n = new Node;
            n->get_parent() = curr;
            curr->set_child(key.back(), n);
        }
        curr = n;
        len++;
        if (node->meaning.meaning.empty()) return;
        n->meaning.meaning = node->meaning.meaning;
        n->meaning.type = node->meaning.type;
    });
    return result;
}

/**
 * TODO - Creates a new dictionary, consisting only of the words
 * starting with the given key.
*/
Dictionary Dictionary::filter_starting_word(const char* key) const{
    if (key == nullptr || key[0] == '\0') {
        Dictionary result(*this);
        return result;
    }
    Dictionary result("");
    string target_key(key);
    Node* target_node = nullptr;
    
    foreach([&] (Node* node, vector<int>& key) mutable {
        Node* curr = target_node;
        string keystr;
        for (vector<int>::const_iterator itr = key.begin(); itr < key.end(); itr++) {
            if (curr != nullptr && itr - key.begin() >= target_key.length() && itr + 1 < key.end()) curr = (*curr)[*itr];
            keystr.push_back(index_to_character(*itr));
        }

        if (keystr.length() < target_key.length()) return;
        if (keystr.substr(0, target_key.length()).compare(target_key) != 0) return;

        Node* n = new Node;
        if (keystr.compare(target_key) == 0) {
            n->meaning.meaning = node->meaning.meaning;
            n->meaning.type = node->meaning.type;
            target_node = n;
            return;
        }
        n->get_parent() = curr;
        curr->set_child(key.back(), n);
        n->meaning.meaning = node->meaning.meaning;
        n->meaning.type = node->meaning.type;
    });

    if (target_node == nullptr) return result;

    Node* curr = result.root;
    for (int i = 0; key[i + 1] != '\0'; i++) {
        Node* n = new Node;
        n->get_parent() = curr;
        curr->set_child(character_to_index(key[i]), n);
        curr = n;
    }
    target_node->get_parent() = curr;
    curr->set_child(character_to_index(target_key.back()), target_node);

    return result;
}

Dictionary Dictionary::operator+(const Dictionary& d2) const{
    return merge(d2);
}

Dictionary Dictionary::operator+(Dictionary&& d2) const{
    return merge(move(d2));
}