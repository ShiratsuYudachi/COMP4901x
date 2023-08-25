#include "Monster.h"
#include <cmath>

// write your code here

Monster::Monster(int x, int y) : MapUnit(x, y) {}
Monster::~Monster() {}
bool Monster::is_active() const { return active; }
void Monster::set_active()
{
    if (is_valid())
        active = true;
}
void Monster::recover_hp(int hp)
{
    cur_hp += hp;
    if (cur_hp > max_hp)
        cur_hp = max_hp;
}
UnitType Monster::get_unit_type() const { return UnitType::MONSTER; }
bool Monster::is_blocked() const { return is_valid(); }
string Monster::get_display_str() const
{
    if (!is_valid())
        return SYM_EMPTY;
    else
    {
        if (is_discovered())
            return get_monster_str();
        else
            return SYM_DANGER;
    }
}
//i think it will be better to make both Monster & Player inherit class Entity
int Monster::attacked_by(int atk_)
{
    if (!is_valid())
    {
        return 0;
    }
    int damage = atk_ - def;
    if (damage > 0)
    {
        cur_hp -= damage;
        if (cur_hp <= 0)
        {
            invalidate();
            active = false;
            return 1;
        }
    }
    return 0;
}
void Monster::follow(const Player &p, MapUnit *map[][MAP_SIZE])
{
    int px, py;
    p.get_position(px, py);
    int dx = px - x, dy = py - y, dstx = 0, dsty = 0, dist = dx+dy;
    if (dist == 1)
        return;
    
    auto move = [=](int targetX, int targetY){
        if (!map[targetX][targetY]->is_blocked())
        {
            map[x][y] = new EmptyLand(x, y);
            delete map[dstx][y];
            map[dstx][y] = this;
            this->x = dstx;
            return;
        }
    };

    if (dx != 0)
    {
        dstx = x + dx / abs(dx);
        move(dstx,y);
    }
    else if (dy != 0)
    {
        dsty = y + dy / abs(dy);
        move(x,dsty);
    }
}
