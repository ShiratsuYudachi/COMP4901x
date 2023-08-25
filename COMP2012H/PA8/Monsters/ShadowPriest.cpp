#include "ShadowPriest.h"

ShadowPriest::ShadowPriest(int x, int y) : Monster(x, y)
{
    cur_hp = max_hp = 15;
    atk = 5, def = 2;
}

//write your code here
ShadowPriest::~ShadowPriest() {}
string ShadowPriest::get_monster_str() const
{
    string s = "S";
    if (cur_hp < 10)
        s += "0";
    s += to_string(cur_hp);
    return s;
}
void ShadowPriest::action(Player &p, MapUnit *map[][MAP_SIZE])
{
    int px, py;
    p.get_position(px, py);
    int dx = px - x, dy = py - y;
    if (abs(dx) + abs(dy) <= 1)
        p.attacked_by(atk);
    
    for (int dx = -1, dy = -1; dx < 2 && dy < 2; dx = dx<2? dx+1: -1,dy+= dx<2? 0: 1)
    {
        if ((y + dy < 0 || y + dy >= MAP_SIZE) || (x + dx < 0 || x + dx >= MAP_SIZE))
            continue;
        if (dx == 0 && dy == 0)
            continue;
        MapUnit *mu = map[x + dx][y + dy];
        if (mu->is_valid() && mu->get_unit_type() == UnitType::MONSTER)
        {
            ((Monster *)mu)->recover_hp(atk);
        }
    }
}
