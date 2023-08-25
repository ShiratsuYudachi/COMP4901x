#include "Gem.h"


//write your codes here
Gem::Gem(int x, int y, GemType gem_type) : Item(x, y), gtype(gem_type){}
Gem::~Gem() {}
void Gem::triggered_by(Player &p)
{
    if (is_valid())
    {
        if ((gtype==GemType::EMERALD && p.get_role() == Role::ARCHER)||
            (gtype==GemType::EMERALD && p.get_role() == Role::WARRIOR)||
            (gtype==GemType::SAPPHIRE && p.get_role() == Role::MAGE))
        {
            invalidate();
        }
    }
}


string Gem::get_item_str() const
{
    switch (gtype)
    {
    case GemType::EMERALD:
        return SYM_EMERALD;
        break;
    case GemType::RUBY:
        return SYM_RUBY;
        break;
    case GemType::SAPPHIRE:
        return SYM_SAPPHIRE;
        break;
    default:
        return "";
        break;
    }
}