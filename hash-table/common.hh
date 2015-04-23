#ifndef COMMON_HH
#define COMMON_HH

template <typename Key, typename Value>
class kv
{
	Key _key;
	Value _value;

public:
	kv (Key key, Value value)
		: _key (key),
		  _value (value)
	{
	}

	kv (kv&&) = default;
	kv (const kv&) = delete;
	kv& operator = (kv&&) = default;
	kv& operator = (const kv&) = delete;

	const Key& key () const
	{
		return _key;
	}

	Value& value ()
	{
		return _value;
	}

	const Value& value () const
	{
		return _value;
	}
};

template <typename Key, typename Value>
const Key& by_key (const kv <Key, Value>& pair)
{
	return pair.key ();
}

#endif
