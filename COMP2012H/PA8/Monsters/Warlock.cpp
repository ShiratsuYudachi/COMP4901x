#include "Warlock.h"

Warlock::Warlock(int x, int y) : Monster(x, y)
{
    cur_hp = max_hp = 15;
    atk = 5, def = 1;
}

//write your code here


void Warlock::action(Player &p, MapUnit *map[][MAP_SIZE])
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
        if (((x + dx) != px || (y + dy) != py) && !map[x + dx][y + dy]->is_blocked())
            {
                delete map[x + dx][y + dy];
                map[x + dx][y + dy] = new Zombie(x + dx, y + dy);
            }
    }
}


