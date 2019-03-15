
mode <number>:
{
	time: [<expr>, <expr>];
	
	invt:
	{
		<prop>;
		...
		<prop>;
	}

	flow:
	{
		d/dt[<var>] = <expr>;
		...
		d/dt[<var>] = <expr>;
	}

	jump(<number>, <prop>):
	{
		<var>' = <expr>;
		...
		<var>' = <expr>;
	}

	sample(<expr>):
	{
		<var>' = <expr>;
		...
		<var>' = <expr>;
	}
}

init(<number>):
		<var>' = <expr>;
		...
		<var>' = <expr>;


goal(<number>):
<prop>;