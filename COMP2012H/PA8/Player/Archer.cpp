#include "Archer.h"

// Please do not change the following already implemented code
void Archer::level_up()
{
    max_hp += 2;
    cur_hp = max_hp;
    atk += 3;
    def += 2;
    max_mp += 1;
    level += 1;
    max_exp += 2;
}

//write your code here

Archer::Archer(int x_, int y_, const string &name) : Player(x_, y_, name){
    atk = 4;
    def = 3;
    cur_hp = 12;
    max_hp = 12;
}
Archer::~Archer() {}

Role Archer::get_role() const {return Role::ARCHER;}

int Archer::get_range() const{return 3;}

int Archer::skill(int &atk_, int &range_) {
    if (cur_mp>0){
        cur_mp-=1;
        atk_ = MAX_ATK;
        range_ = 3;
    }
    else return 1; 
}