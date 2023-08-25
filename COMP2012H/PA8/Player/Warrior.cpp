#include "Warrior.h"

// Please do not change the following already implemented code

void Warrior::level_up()
{
    max_hp += 3;
    cur_hp = max_hp;
    atk += 2;
    def += 1;
    max_mp += 1;
    level += 1;
}

//write your code here

Warrior::Warrior(int x_, int y_, const string &name) : Player(x_, y_, name){
    atk = 6;
    def = 3;
    cur_hp = 15;
    max_hp = 15;
}
Warrior::~Warrior() {}

Role Warrior::get_role() const {return Role::WARRIOR;}

int Warrior::get_range() const{return 1;}

int Warrior::skill(int &atk, int &range) { return 1; }

void Warrior::attacked_by(int atk_){
    int damage = atk - def;
    if (damage>=cur_hp && cur_mp>=0){
        cur_mp-=1;
        cur_hp+=max_hp/2;
    }
    else if (damage>0){
        cur_hp = cur_hp - damage;
    }
    return;
}






